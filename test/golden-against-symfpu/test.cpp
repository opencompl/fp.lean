#include <cstddef>
#include "symfpu/baseTypes/simpleExecutable.h"
#include "symfpu/core/unpackedFloat.h"
#include "symfpu/core/packing.h"
#include "symfpu/core/add.h"

using namespace symfpu::simpleExecutable;
typedef symfpu::unpackedFloat<traits> uf;

int main() {
  traits::fpt format(5,3);
  traits::ubv packed1(8,0x02), packed2(8,0x02);
  printf("%d\n", uf::exponentWidth(format));

  uf unpacked1(symfpu::unpack<traits>(format, packed1));
  uf unpacked2(symfpu::unpack<traits>(format, packed2));

  uf added(symfpu::add<traits>(format, traits::RNE(), unpacked1, unpacked2, traits::prop(true)));
  traits::ubv repacked(symfpu::pack<traits>(format, added));

  printf("%x\n", repacked);
  return 0;
}

