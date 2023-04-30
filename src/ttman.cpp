#include "ttman.h"

using namespace Ttman;

const Man::word Man::vars[] = {0xaaaaaaaaaaaaaaaaull,
                               0xccccccccccccccccull,
                               0xf0f0f0f0f0f0f0f0ull,
                               0xff00ff00ff00ff00ull,
                               0xffff0000ffff0000ull,
                               0xffffffff00000000ull};

const Man::word Man::ones[] = {0x0000000000000001ull,
                               0x0000000000000003ull,
                               0x000000000000000full,
                               0x00000000000000ffull,
                               0x000000000000ffffull,
                               0x00000000ffffffffull,
                               0xffffffffffffffffull};

