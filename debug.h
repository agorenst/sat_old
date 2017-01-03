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
#define TRACE(...) printf(__VA_ARGS__)
#else
#define TRACE(...)
#endif


#endif
