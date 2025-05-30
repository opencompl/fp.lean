#include <cstddef>
#include "symfpu/baseTypes/simpleExecutable.h"
#include "symfpu/core/unpackedFloat.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/fma.h"
#include <bitset>
#include <functional>

using namespace symfpu::simpleExecutable;
typedef symfpu::unpackedFloat<traits> uf;
typedef traits::ubv ubv;
traits::rm modes[5] = { 
  traits::RNA(), 
  traits::RNE(), 
  traits::RTN(), 
  traits::RTP(), 
  traits::RTZ() 
};

// Note: This fails assertions because symfpu assumes the exponent is shorter than the
// mantissa
void test_rounding(void) {
  // 10-bit E5M4 float
  traits::fpt inFormat(5,5);
  // 8-bit E5M2 float
  traits::fpt outFormat(5,3);
  for (traits::rm mode : modes) {
    for (uint64_t i = 0; i < (1 << 1); i++) {
      traits::ubv packed(10, i);
      uf unpacked(symfpu::unpack<traits>(inFormat, packed));
  
      uf rounded(symfpu::rounder<traits>(outFormat, mode, unpacked));
      traits::ubv repacked(symfpu::pack<traits>(outFormat, rounded));
      printf("%d\n", repacked.contents());
    }
  }
}

std::string to_mode(traits::rm mode) {
  if (mode == traits::RNA()) return "RNA";
  if (mode == traits::RNE()) return "RNE";
  if (mode == traits::RTN()) return "RTN";
  if (mode == traits::RTP()) return "RTP";
  if (mode == traits::RTZ()) return "RTZ";
  return "???";
}

// SymFPU already performs NaN normalisation
std::bitset<8> to_bits(ubv bitvec, bool normNaN = false) {
  std::bitset<8> result;
  uint64_t c = bitvec.contents();
  for (int i = 0; i < 8; i++) {
    result[7-i] = (c >> (7-i)) & 1;
  }
  return result;
}

// Test binary operation on 8 bits.
void test_ternop(std::string name, 
  std::function<ubv(traits::rm, ubv, ubv, ubv)> f) {
  for (traits::rm mode : modes) {
    for (uint64_t i = 0; i < (1<<8); i++) {
      for (uint64_t j = 0; j < (1<<8); j++) {
        for (uint64_t k = 0; k < (1<<8); k++) {
            ubv packed1(8, i), packed2(8, j), packed3(8, k);
            ubv result = f(mode, packed1, packed2, packed3);
            std::cout << name << "," << to_mode(mode) << "," << \
                to_bits(packed1) << "," << to_bits(packed2) << "," << to_bits(packed3) << "," << \
                to_bits(result, true) << "\n";
        }
      }
    }
  }
}

traits::fpt e3m4(3,5);
int main() {

  test_ternop("fma", [](traits::rm mode, ubv a, ubv b, ubv c) {
    uf ua(symfpu::unpack<traits>(e3m4, a)), 
       ub(symfpu::unpack<traits>(e3m4, b)), 
       uc(symfpu::unpack<traits>(e3m4, c));
    
    uf ud(symfpu::fma<traits>(e3m4, mode, ua, ub, uc));
    
    return symfpu::pack<traits>(e3m4, ud);
  });


  return 0;
}

