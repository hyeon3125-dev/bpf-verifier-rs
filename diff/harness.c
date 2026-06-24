/*
 * Differential harness: links the *real* kernel tnum.c + cnum.c (via userspace
 * stubs) and answers queries on stdin so the Rust model can be checked against
 * the genuine C implementation. One query per line:
 *
 *   tnum_add   <av> <am> <bv> <bm>            -> <rv> <rm>
 *   tnum_sub   <av> <am> <bv> <bm>            -> <rv> <rm>
 *   tnum_and   <av> <am> <bv> <bm>            -> <rv> <rm>
 *   tnum_or    <av> <am> <bv> <bm>            -> <rv> <rm>
 *   tnum_xor   <av> <am> <bv> <bm>            -> <rv> <rm>
 *   tnum_mul   <av> <am> <bv> <bm>            -> <rv> <rm>
 *   c64_isect  <ab> <as> <bb> <bs>            -> <rb> <rs>
 *   c64_add    <ab> <as> <bb> <bs>            -> <rb> <rs>
 *   c64_subset <ab> <as> <bb> <bs>            -> <0|1>
 *   c32_from64 <ab> <as>                      -> <rb> <rs>
 *   c64_c32    <ab> <as> <bb> <bs>            -> <rb> <rs>   (cnum64_cnum32_intersect)
 *
 * All scalars are decimal u64 (cnum32 fields fit in u32).
 */
#include <linux/tnum.h>
#include <linux/cnum.h>
#include <stdio.h>
#include <string.h>

int main(void)
{
	char op[32];
	unsigned long long a, b, c, d;

	while (scanf("%31s", op) == 1) {
		if (!strcmp(op, "tnum_add") || !strcmp(op, "tnum_sub") ||
		    !strcmp(op, "tnum_and") || !strcmp(op, "tnum_or") ||
		    !strcmp(op, "tnum_xor") || !strcmp(op, "tnum_mul")) {
			if (scanf("%llu %llu %llu %llu", &a, &b, &c, &d) != 4) break;
			struct tnum x = { .value = a, .mask = b };
			struct tnum y = { .value = c, .mask = d };
			struct tnum r;
			if      (!strcmp(op, "tnum_add")) r = tnum_add(x, y);
			else if (!strcmp(op, "tnum_sub")) r = tnum_sub(x, y);
			else if (!strcmp(op, "tnum_and")) r = tnum_and(x, y);
			else if (!strcmp(op, "tnum_or"))  r = tnum_or(x, y);
			else if (!strcmp(op, "tnum_xor")) r = tnum_xor(x, y);
			else                              r = tnum_mul(x, y);
			printf("%llu %llu\n", (unsigned long long)r.value,
			       (unsigned long long)r.mask);
		} else if (!strcmp(op, "c64_isect") || !strcmp(op, "c64_add") ||
			   !strcmp(op, "c64_subset")) {
			if (scanf("%llu %llu %llu %llu", &a, &b, &c, &d) != 4) break;
			struct cnum64 x = { .base = a, .size = b };
			struct cnum64 y = { .base = c, .size = d };
			if (!strcmp(op, "c64_subset")) {
				printf("%d\n", cnum64_is_subset(x, y) ? 1 : 0);
			} else {
				struct cnum64 r = !strcmp(op, "c64_isect")
					? cnum64_intersect(x, y)
					: cnum64_add(x, y);
				printf("%llu %llu\n", (unsigned long long)r.base,
				       (unsigned long long)r.size);
			}
		} else if (!strcmp(op, "c32_from64")) {
			if (scanf("%llu %llu", &a, &b) != 2) break;
			struct cnum64 x = { .base = a, .size = b };
			struct cnum32 r = cnum32_from_cnum64(x);
			printf("%llu %llu\n", (unsigned long long)r.base,
			       (unsigned long long)r.size);
		} else if (!strcmp(op, "c64_c32")) {
			if (scanf("%llu %llu %llu %llu", &a, &b, &c, &d) != 4) break;
			struct cnum64 x = { .base = a, .size = b };
			struct cnum32 y = { .base = (u32)c, .size = (u32)d };
			struct cnum64 r = cnum64_cnum32_intersect(x, y);
			printf("%llu %llu\n", (unsigned long long)r.base,
			       (unsigned long long)r.size);
		} else {
			fprintf(stderr, "unknown op: %s\n", op);
			return 2;
		}
	}
	return 0;
}
