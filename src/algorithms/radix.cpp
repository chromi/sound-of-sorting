/******************************************************************************
 * src/algorithms/radix.cpp
 *
 * Implementations of radix sorting algorithms.
 *
 * Note that these implementations may not be as good/fast as possible. Some
 * are modified so that the visualization is more instructive.
 *
 * Futhermore, some algorithms are annotated using the mark() and watch()
 * functions from SortArray. These functions add colors to the illustratation
 * and thereby makes the algorithm's visualization easier to explain.
 *
 ******************************************************************************
 * Copyright (C) 2013-2014 Timo Bingmann <tb@panthema.net>
 * Copyright (C) 2021 Jonathan Morton <chromatix99@gmail.com>
 *
 * This program is free software: you can redistribute it and/or modify it
 * under the terms of the GNU General Public License as published by the Free
 * Software Foundation, either version 3 of the License, or (at your option)
 * any later version.
 *
 * This program is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
 * more details.
 *
 * You should have received a copy of the GNU General Public License along with
 * this program.  If not, see <http://www.gnu.org/licenses/>.
 *****************************************************************************/

#include "SortAlgo.h"
#include "algorithms/radix.h"

#include <numeric>

// ****************************************************************************
// *** Radix Sort (counting sort, most significant digit (MSD) first, in-place redistribute)

// by myself (Timo Bingmann)

void RadixSortMSD(SortArray& A, size_t lo, size_t hi, size_t depth)
{
	A.mark(lo); A.mark(hi-1);

	// radix and base calculations
	const unsigned int RADIX = 4;

	unsigned int pmax = floor( log(A.array_max()+1) / log(RADIX) );
	ASSERT(depth <= pmax);

	size_t base = pow(RADIX, pmax - depth);

	// count digits
	std::vector<size_t> count(RADIX, 0);

	for (size_t i = lo; i < hi; ++i)
	{
		size_t r = A[i].get() / base % RADIX;
		ASSERT(r < RADIX);
		count[r]++;
	}

	// inclusive prefix sum
	std::vector<size_t> bkt(RADIX, 0);
	std::partial_sum(count.begin(), count.end(), bkt.begin());

	// mark bucket boundaries
	for (size_t i = 0; i < bkt.size(); ++i) {
		if (bkt[i] == 0) continue;
		A.mark(lo + bkt[i]-1, 3);
	}

	// reorder items in-place by walking cycles
	for (size_t i=0, j; i < (hi-lo); )
	{
		while ( (j = --bkt[ (A[lo+i].get() / base % RADIX) ]) > i )
		{
			A.swap(lo + i, lo + j);
		}
		i += count[ (A[lo+i].get() / base % RADIX) ];
	}

	A.unmark_all();

	// no more depth to sort?
	if (depth+1 > pmax) return;

	// recurse on buckets
	size_t sum = lo;
	for (size_t i = 0; i < RADIX; ++i)
	{
		if (count[i] > 1)
			RadixSortMSD(A, sum, sum+count[i], depth+1);
		sum += count[i];
	}
}

void RadixSortMSD(SortArray& A)
{
	return RadixSortMSD(A, 0, A.size(), 0);
}

// ****************************************************************************
// *** Radix Sort (counting sort, least significant digit (LSD) first, out-of-place redistribute)

// by myself (Timo Bingmann)

void RadixSortLSD(SortArray& A)
{
	// radix and base calculations
	const unsigned int RADIX = 4;

	unsigned int pmax = ceil( log(A.array_max()+1) / log(RADIX) );

	for (unsigned int p = 0; p < pmax; ++p)
	{
		size_t base = pow(RADIX, p);

		// count digits and copy data
		std::vector<size_t> count(RADIX, 0);
		std::vector<value_type> copy(A.size());

		for (size_t i = 0; i < A.size(); ++i)
		{
			size_t r = (copy[i] = A[i]).get() / base % RADIX;
			ASSERT(r < RADIX);
			count[r]++;
		}

		// exclusive prefix sum
		std::vector<size_t> bkt(RADIX+1, 0);
		std::partial_sum(count.begin(), count.end(), bkt.begin()+1);

		// mark bucket boundaries
		for (size_t i = 0; i < bkt.size()-1; ++i) {
			if (bkt[i] >= A.size()) continue;
			A.mark(bkt[i], 3);
		}

		// redistribute items back into array (stable)
		for (size_t i=0; i < A.size(); ++i)
		{
			size_t r = copy[i].get() / base % RADIX;
			A.set( bkt[r]++, copy[i] );
		}

		A.unmark_all();
	}
}

