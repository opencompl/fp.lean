#include "floatx.hpp"
#include <iostream>
#include <functional>

typedef flx::floatx<5,2> e5m2;
typedef flx::float_traits<e5m2>::backend_float bf;

e5m2 cons_fp8(uint8_t arg) {
    return flx::detail::construct_number<5,2>(std::bitset<8>(arg));
}

constexpr std::bitset<8> nanBits{0b01111110};
std::bitset<8> to_bits(e5m2 arg, bool normNaN = false) {
    std::bitset<8> argBits = flx::detail::get_fullbit_representation_BS<5,2>(bf(arg));
    if (normNaN && 
        ((argBits.to_ulong() >> 2) & 0b11111) == 0b11111 && 
        ((argBits.to_ulong() & 3) != 0)) {
        return nanBits;
    }
    return argBits;
}

void test_binop(std::string name, std::function<e5m2(e5m2,e5m2)> f) {
    for (uint16_t i = 0; i < (1<<8); i++) {
        for (uint16_t j = 0; j < (1<<8); j++) {
            e5m2 a = cons_fp8(static_cast<uint8_t>(i));
            e5m2 b = cons_fp8(static_cast<uint8_t>(j));
            e5m2 c = f(a,b);
            std::cout << name << "," << "RNE" << "," << \
                to_bits(a) << "," << to_bits(b) << "," << \
                to_bits(c, true) << "\n";
        }
    }
}

void test_predi(std::string name, std::function<bool(e5m2,e5m2)> f) {
    for (uint16_t i = 0; i < (1<<8); i++) {
        for (uint16_t j = 0; j < (1<<8); j++) {
            e5m2 a = cons_fp8(static_cast<uint8_t>(i));
            e5m2 b = cons_fp8(static_cast<uint8_t>(j));
            bool c = f(a,b);
            std::cout << name << "," << "RNE" << "," << \
                to_bits(a) << "," << to_bits(b) << "," << \
                (c ? "1" : "0") << "\n";
        }
    }
}

int main() {
    test_binop("add", [](e5m2 a, e5m2 b) { return a + b; });
    test_predi("lt" , [](e5m2 a, e5m2 b) { return a < b; });
    test_binop("mul", [](e5m2 a, e5m2 b) { return a * b; });
    test_binop("div", [](e5m2 a, e5m2 b) { return a / b; });
    return 0;
}
