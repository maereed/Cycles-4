#include <stdlib.h>
#include <stdio.h>

#define MEMSIZE 1048576

static int little_endian, icount, *instruction;
static int mem[MEMSIZE / 4];

int regDestination[8] = {0};
int resultsAvailable[8] = {0};
static int cycles = 0;
static int clock = 6;
static int flushCount = 0;
static int bubbleCount = 0;


static int Convert(unsigned int x)
{
  return (x >> 24) | ((x >> 8) & 0xff00) | ((x << 8) & 0xff0000) | (x << 24);
}

static int Fetch(int pc)
{
  pc = (pc - 0x00400000) >> 2;
  if ((unsigned)pc >= icount) {
    fprintf(stderr, "instruction fetch out of range\n");
    exit(-1);
  }
  return instruction[pc];
}

static int LoadWord(int addr)
{
  if (addr & 3 != 0) {
    fprintf(stderr, "unaligned data access\n");
    exit(-1);
  }
  addr -= 0x10000000;
  if ((unsigned)addr >= MEMSIZE) {
    fprintf(stderr, "data access out of range\n");
    exit(-1);
  }
  return mem[addr / 4];
}

static void StoreWord(int data, int addr)
{
  if (addr & 3 != 0) {
    fprintf(stderr, "unaligned data access\n");
    exit(-1);
  }
  addr -= 0x10000000;
  if ((unsigned)addr >= MEMSIZE) {
    fprintf(stderr, "data access out of range\n");
    exit(-1);
  }
  mem[addr / 4] = data;
}

/*******************************
    Checking for Dependencies
*******************************/

static void Dependencies(int currentData, int stage){
  int i;

  //Need to traverse through the for loop to find the element the data might
  //be saved in, once found, break
  for(i=0; i < 8; i++){
    if(regDestination[i] == currentData)
      break;
  }

  //Now check if bubbles are needed

  if (resultsAvailable[i] > stage ){ //if the stage avial is greater than stage needed, then add bubbles
      bubbleCount += resultsAvailable[i] - stage;
      NOP(resultsAvailable[i] - stage);
  }

}

/*******************************
    Updating Pipeline

**********************************
Function used to update the pipe-
line with new information
*******************************/

static void Pipeline(int avail, int reg){
  int i;

//*****Set up for stage available array ************
      //update data to reflect that one cycle has passed
      for(i = 0; i < 8; i++){
        if(resultsAvailable[i] != 1){
          resultsAvailable[i] = resultsAvailable[i] - 1; //subtract one each time, since one stage closer to completing results
        }else
          resultsAvailable[i]=0;

      }

    //*****Set up for arrays ************
    //move everything right one element
    for(i = 7; i > 0; i--){
      regDestination[i]= regDestination[i-1];
      resultsAvailable[i]=resultsAvailable[i-1];
    }

    // set new data to the first element in array
    resultsAvailable[0]= avail;
    regDestination[0] = reg;

}

static void nop(int stalls){
  while (stalls != 0){
    Pipeline(-1, -1);
  }
}

static void Interpret(int start)
{
  register int instr, opcode, rs, rt, rd, shamt, funct, uimm, simm, addr;
  register int pc, hi, lo;
  int reg[32];
  register int cont = 1, count = 0, i;
  register long long wide;

  lo = hi = 0;
  pc = start;
  for (i = 1; i < 32; i++) reg[i] = 0;
  reg[28] = 0x10008000;  // gp
  reg[29] = 0x10000000 + MEMSIZE;  // sp


  while (cont) {
    count++;
    instr = Fetch(pc);
    pc += 4;
    reg[0] = 0;  // $zero

    opcode = (unsigned)instr >> 26;
    rs = (instr >> 21) & 0x1f;
    rt = (instr >> 16) & 0x1f;
    rd = (instr >> 11) & 0x1f;
    shamt = (instr >> 6) & 0x1f;
    funct = instr & 0x3f;
    uimm = instr & 0xffff;
    simm = ((signed)uimm << 16) >> 16;
    addr = instr & 0x3ffffff;


    switch (opcode) {
      case 0x00:
        switch (funct) {
          case 0x00:  reg[rd] = reg[rs] << shamt;

          break;/* sll */
          case 0x03:  reg[rd] = reg[rs] >> (signed)shamt;
          break;/* sra */
          case 0x08:  pc = reg[rs];
                                                        flushCount += 2;
          break;/* jr */
          case 0x10:  reg[rd] = hi;
          break; /* mfhi */
          case 0x12:  reg[rd] = lo;
          break;/* mflo */
          case 0x18:  wide = reg[rs];
                      wide *= reg[rt];
                      lo = wide & 0xffffffff;
                      hi = wide >> 32;
          break;/* mult */
          case 0x1a:  if (reg[rt] == 0) {
                        fprintf(stderr, "division by zero: pc = 0x%x\n", pc-4);
                        cont = 0;
                      }else {
                        lo = reg[rs] / reg[rt];
                        hi = reg[rs] % reg[rt];
                      }
          break;/* div */
          case 0x21:  reg[rd] = reg[rs] + reg[rt];
          break;/* addu */
          case 0x23:  reg[rd] = reg[rs] - reg[rt];
          break;/* subu */
          case 0x2a:  if(reg[rs] < reg[rt]){
                        reg[rd] = 1;
                      }else{
                        reg[rd]=0;
                      }
          break;/* slt */
          default: fprintf(stderr, "unimplemented instruction: pc = 0x%x\n", pc-4); cont = 0;
        }
        break;
      case 0x02:  pc = (pc & 0xf0000000) + addr * 4;
                                                          flushCount +=2;
      break;/* j */
      case 0x03: reg[31] = pc; pc = (pc & 0xf0000000) + addr * 4;
                                                          flushCount +=2;
      break;/* jal */
      case 0x04:  if(reg[rs] == reg[rt]){
                    pc = pc + simm * 4;
                                  /*if taken*/            flushCount +=2;
                  }
      break;/* beq */
      case 0x05:  if(reg[rs] != reg[rt]){
                    pc = pc + simm * 4;
                                  /*if taken*/            flushCount +=2;
                  }
      break;/* bne */
      case 0x09:  reg[rt] = reg[rs] + simm;
      break;/* addiu */
      case 0x0c:  reg[rt] = reg[rs] &  uimm;
      break;/* andi */
      case 0x0f:  reg[rt] = simm << 16;
      break;/* lui */
      case 0x1a: /* trap */
        switch (addr & 0xf) {
          case 0x00: printf("\n");
          break;
          case 0x01: printf(" %d ", reg[rs]);
          break;
          case 0x05: printf("\n? "); fflush(stdout); scanf("%d", &reg[rt]);
          break;
          case 0x0a: cont = 0;
          break;
          default: fprintf(stderr, "unimplemented trap: pc = 0x%x\n", pc-4); cont = 0;
        }
        break;
      case 0x23:  reg[rt] = LoadWord(reg[rs] + simm);
      break;  /* lw */ // call LoadWord function
      // instruction counter
      case 0x2b:  StoreWord(reg[rt], reg[rs] + simm);
      break;  /* sw */ // call StoreWord function
      default: fprintf(stderr, "unimplemented instruction: pc = 0x%x\n", pc-4); cont = 0;
    }

  }

  printf("\nprogram finished at pc = 0x%x  (%d instructions executed)\n", pc, count);
  cycles = count + 7 + bubbleCount + flushCount;
  printf("Number of cycles: %i \n", cycles);
  printf("Number of bubbles: %i \n", bubbleCount);
  printf("Number of flushes: %i \n", flushCount);

}

int main(int argc, char *argv[])
{
  int c, start;
  FILE *f;

  memcpy(&regDestination, &(int [8]){ 0 }, sizeof regDestination);
  memcpy(&resultsAvailable, &(int [8]){ 0 }, sizeof resultsAvailable);

  printf("CS3339 -- MIPS Interpreter\n");
  if (argc != 2) {fprintf(stderr, "usage: %s executable\n", argv[0]); exit(-1);}
  if (sizeof(int) != 4) {fprintf(stderr, "error: need 4-byte integers\n"); exit(-1);}
  if (sizeof(long long) != 8) {fprintf(stderr, "error: need 8-byte long longs\n"); exit(-1);}

  c = 1;
  little_endian = *((char *)&c);
  f = fopen(argv[1], "r+b");
  if (f == NULL) {fprintf(stderr, "error: could not open file %s\n", argv[1]); exit(-1);}
  c = fread(&icount, 4, 1, f);
  if (c != 1) {fprintf(stderr, "error: could not read count from file %s\n", argv[1]); exit(-1);}
  if (little_endian) {
    icount = Convert(icount);
  }
  c = fread(&start, 4, 1, f);
  if (c != 1) {fprintf(stderr, "error: could not read start from file %s\n", argv[1]); exit(-1);}
  if (little_endian) {
    start = Convert(start);
  }

  instruction = (int *)(malloc(icount * 4));
  if (instruction == NULL) {fprintf(stderr, "error: out of memory\n"); exit(-1);}
  c = fread(instruction, 4, icount, f);
  if (c != icount) {fprintf(stderr, "error: could not read (all) instructions from file %s\n", argv[1]); exit(-1);}
  fclose(f);
  if (little_endian) {
    for (c = 0; c < icount; c++) {
      instruction[c] = Convert(instruction[c]);
    }
  }

  printf("running %s\n\n", argv[1]);
  Interpret(start);

}

