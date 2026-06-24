/* userspace stub for differential build */
#pragma once
#include <linux/types.h>

/* find-last-set on 64-bit: 0 if x==0 else (index of MSB)+1 */
static inline int fls64(u64 x) { return x ? 64 - __builtin_clzll(x) : 0; }

#ifndef min
#define min(a, b) ((a) < (b) ? (a) : (b))
#endif
#ifndef max
#define max(a, b) ((a) > (b) ? (a) : (b))
#endif
#ifndef swap
#define swap(a, b) do { __typeof__(a) __t = (a); (a) = (b); (b) = __t; } while (0)
#endif

#ifndef EXPORT_SYMBOL_GPL
#define EXPORT_SYMBOL_GPL(x)
#endif
