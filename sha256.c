/*
 * An implementation of SHA-2/256, adapted from Wikipedia.
 */
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <time.h>

/* "round" constants; fractional parts of first 64 primes */
unsigned k[] = {
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
};

/* rotate 32 bit unsigned i right, n bits */
unsigned ror(unsigned i, int n)
{
  return (0xffffffff)&((i>>n)|(i<<(32-n)));
}

/* convert 64 bit unsigned x to big-endian.  terrifying. */
unsigned long bend64(unsigned long x)
{
  int i;
  unsigned long result = 0x0;
  for (i = 0; i < 64; i+=8) {
    result = (result << 8) | ((x>>i) & 0xff);
  }
  return result;
}

/* convert 32 bit unsigned x to big-endian.  annoying. */
unsigned bend32(unsigned x)
{
  int i;
  unsigned result = 0x0;
  for (i = 0; i < 32; i+=8) {
    result = (result << 8) | ((x >> i) & 0xff);
  }
  return result;
}


/* turn n word digest of 32-bit values into a little endian buffer
 * (on most machines, this could be trivial)
 */
unsigned char *lends(unsigned *digest, int n)
{
  unsigned char *result = (unsigned char*)calloc(n*4+1,1);
  unsigned char *p = result;
  int i, j;
  for (i = 0; i < n; i++) {
    for (j = 3; j >= 0; j--) {
      *p++ = (digest[i] >> (j*8)) & 0xff;
    }
  }
  return result;
}

/*
 * Compute the digest (8 unsigned integers, read in big-endian order)
 * of a 'l' byte message 's'.
 */
unsigned char *sha256(unsigned char *s, int l)
{
  static unsigned H[8] = {0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
		   0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19};
  static unsigned w[64] = {0}; // message "schedule"

  /*
   * message format:
   *  <message bits>10...<message bit length as 64 bit value>
   * where 0... is a string of zeros sufficient to bring total
   *length to a multiple of 512 bits.
   */
  int chbeg,i,j;
  int L = 8*l; // message bit length
  int K = 512-(0x1ff&(L+1+64)); // Kount of zeros, 0..511
  if (K == 512) K = 0; // silliness
  int sz = (L+1+K+64)/8; // total message size (bytes)
  unsigned char *msg = (unsigned char*)calloc(sz+1,1);
  memcpy((char*)msg,s,l);  // copy message
  msg[l] |= 0x80;  // append a 1
  unsigned long *end = (unsigned long*)(msg+sz-8);
  *end = (unsigned long)bend64(l*8); // stick on msg size

  // BEGIN: compute hash of 512 bit (64 byte) chunks of message
  for (chbeg = 0; chbeg < sz; chbeg += 64) {
    unsigned char *p = msg+chbeg;
    
    for (i = 0; i < 16; i++) {
      w[i] = 0;
      for (j = 0; j < 4; j++) {
	w[i] = w[i]<<8 | *p++;
      }
    }
    for (i = 16; i < 64; i++) {
      unsigned int wim15 = w[i-15];
      unsigned int wim2 = w[i-2];
      unsigned s0 = ror(wim15,7) ^ ror(wim15,18) ^ (wim15 >> 3);
      unsigned s1 = ror(wim2,17) ^ ror(wim2,19) ^ (wim2 >> 10);
      w[i] = w[i-16]+s0+w[i-7]+s1;
    }
    unsigned a = H[0];
    unsigned b = H[1];
    unsigned c = H[2];
    unsigned d = H[3];
    unsigned e = H[4];
    unsigned f = H[5];
    unsigned g = H[6];
    unsigned h = H[7];

    for (i = 0; i < 64; i++) {
      unsigned s1 = ror(e,6) ^ ror(e,11) ^ ror(e,25);
      unsigned ch = (e&f)^((~e)&g);
      unsigned temp1  = h+s1+ch+k[i]+w[i];
      unsigned s0 = ror(a,2) ^ ror(a,13) ^ ror(a,22);
      unsigned maj = (a&b) ^ (a&c) ^ (b&c);
      unsigned temp2 = s0+maj;
      h = g;
      g = f;
      f = e;
      e = d+temp1;
      d = c;
      c = b;
      b = a;
      a = temp1+temp2;
    }
    H[0] += a;
    H[1] += b;	   
    H[2] += c;
    H[3] += d;
    H[4] += e;
    H[5] += f;
    H[6] += g;
    H[7] += h;
  }
  return lends(H,32);
}

int main(int argc, char**argv)
{
  char *s = argv[1];
  int i;
  unsigned char *resultstr = sha256((unsigned char*)s,strlen(s));

  printf("0x");
  for (i = 0; i < 32; i++) {
    printf("%02x",resultstr[i]);
  }
  fputc('\n',stdout);
}
