#ifndef DEBUG_H
#define DEBUG_H


// Basic asserts
#ifdef ASSERTS_ON
#include <cassert>
#define ASSERT(x) assert(x)
#else
#define ASSERT(x)
#endif

// Basic logging
#ifdef VERBOSE_ON
#include <cstdio>
#include <iostream>
template<typename T>
void trace(const T& value) {
    std::clog << value;
}
template<typename T, typename... Targs>
void trace(const T& value, const Targs&... Fargs) {
    std::clog << value;
    trace(Fargs...);
}
#define TRACE(...) printf(__VA_ARGS__)
#else
#define trace(...)
#define TRACE(...)
#endif


#endif
