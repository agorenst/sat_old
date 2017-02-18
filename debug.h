#ifndef DEBUG_H
#define DEBUG_H


// Basic asserts
#ifdef ASSERTS_ON
#include <cassert>
#define ASSERT(x) assert(x)
#define DBGSTMT(x) x
#else
#define ASSERT(x)
#define DBGSTMT(x)
#endif

// Basic logging
#ifdef VERBOSE_ON
#include <cstdio>
#include <iostream>
template<typename T>
void TRACE(const T& value) {
    std::clog << value;
}
template<typename T, typename... Targs>
void TRACE(const T& value, const Targs&... Fargs) {
    std::clog << value;
    TRACE(Fargs...);
}
#else
#define TRACE(...)
#endif


#endif
