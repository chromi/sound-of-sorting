/******************************************************************************
 * src/algorithms/merge.cpp
 *
 * Implementations of merge-based sorting algorithms.
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
#include "algorithms/merge.h"

// ****************************************************************************
// *** Merge Sort (out-of-place with sentinels)

// by myself (Timo Bingmann)

void Merge(SortArray& A, size_t lo, size_t mid, size_t hi)
{
	// mark merge boundaries
	A.mark(lo);
	A.mark(mid,3);
	A.mark(hi-1);

	// allocate output
	std::vector<value_type> out(hi-lo);

	// merge
	size_t i = lo, j = mid, o = 0; // first and second halves
	while (i < mid && j < hi)
	{
		// copy out for fewer time steps
		value_type ai = A[i], aj = A[j];

		out[o++] = (ai < aj ? (++i, ai) : (++j, aj));
	}

	// copy rest
	while (i < mid) out[o++] = A[i++];
	while (j < hi) out[o++] = A[j++];

	ASSERT(o == hi-lo);

	A.unmark(mid);

	// copy back
	for (i = 0; i < hi-lo; ++i)
		A.set(lo + i, out[i]);

	A.unmark(lo);
	A.unmark(hi-1);
}

void MergeSort(SortArray& A, size_t lo, size_t hi)
{
	if (lo + 1 < hi)
	{
		size_t mid = (lo + hi) / 2;

		MergeSort(A, lo, mid);
		MergeSort(A, mid, hi);

		Merge(A, lo, mid, hi);
	}
}

void MergeSort(SortArray& A)
{
	return MergeSort(A, 0, A.size());
}

void MergeSortIterative(SortArray& A)
{
	for (size_t s = 1; s < A.size(); s *= 2)
	{
		for (size_t i = 0; i + s < A.size(); i += 2 * s)
		{
			Merge(A, i, i + s,
				std::min(i + 2 * s, A.size()));
		}
	}
}

// ****************************************************************************
// *** In-Place Merge Sort

// By Jonathan Morton.
// Based on https://xinok.wordpress.com/2014/08/17/in-place-merge-sort-demystified-2/
// This is a stable sort with O(N * (log N)^2) worst-case complexity using O(1) extra space (ignoring call stack).
// Hence it is slower than standard mergesort, but faster than insertion sort and uses less memory than standard mergesort.

#define MERGESORT_INPLACE_THRESHOLD (16UL)

void MergeSortSwapBlocks(SortArray& A, const size_t l, const size_t m, const size_t r)
{
	// We have two sorted, adjacent blocks (not necessarily of equal size) of which the last element of the right block sorts before
	// the first element of the left block.  Our task is therefore to exchange them as efficiently as is practical, keeping order.
	const size_t a = r-m, b = m-l;

	assert(a);
	assert(b);

	// We can trivially do this with N swaps, reversing the two blocks and then reversing the concatenated block.  If a swap counts
	// as only 2 array accesses, then this is even an efficient solution.  However, it no longer *looks* very much like a merge,
	// since the blocks are temporarily in reverse order.

	// If the blocks happen to be of equal size, then we can use N/2 swaps and it looks natural.
	if(a == b) {
		for(size_t i=l, j=m; i < m; i++, j++) {
			A.mark_swap(i,j);
			A.swap(i,j);
		}
		return;
	}

	// With unequal sizes, we must shuffle elements around in cycles of order gcd(_L,_R) for it to look like a merge.
	// This results in 2N array accesses and is therefore efficient, but is less intuitive to code up correctly.
	size_t c = a, d = b;

	while(d) {
		size_t e = c % d;
		c = d;
		d = e;
	}
	d = (a+b)/c;

	for(size_t i=0; i < c; i++) {
		size_t x = (a+i)%(a+b);
		value_type t = A[x+l];

		for(size_t j=0; j < d-1; j++) {
			size_t y = (x+b)%(a+b);
			A.set(x+l, A[y+l]);
			A.mark_swap(x+l, y+l);
			x = y;
		}

		A.set(x+l, t);
	}
}

void MergeSortMergeSmall(SortArray& A, const size_t l, const size_t m, const size_t r, const bool root=false)
{
	// To deal with small blocks more efficiently, we could use an insertion sort (preserving the stable-sort property).
	// However, I decided to keep it as a pure mergesort, using a fixed-size temporary array.
	// Elements from the left block are only moved into the temporary array if they can't conveniently be held in the right block.
	// Elements from the right block are always moved directly into the correct position.

	ASSERT(m-l <= MERGESORT_INPLACE_THRESHOLD || r-m <= MERGESORT_INPLACE_THRESHOLD);

	// Deal with trivial and simple cases first:

	// Either of the blocks is zero-length?
	if(m <= l || r <= m)
		return;

	if(root) {
		for(size_t i=l; i < m; i++)
			A.mark(i, 4);
		for(size_t i=m; i < r; i++)
			A.mark(i, 11);
	}

	// Elements already in correct order?
	if(A[m-1] <= A[m])
		return;

	// Single-element blocks in wrong order?
	if(r-l == 2) {
		A.swap(l,m);
		A.mark_swap(l,m);
		return;
	}

	// Entire blocks need swapping?
	if(A[r-1] < A[l]) {
		A.rotate(l, m, r);
		return;
	}

	// Okay, down to business.
	size_t idx[MERGESORT_INPLACE_THRESHOLD] = {0};
	size_t rev[MERGESORT_INPLACE_THRESHOLD] = {0};

	if(m-l <= MERGESORT_INPLACE_THRESHOLD && (m-l >= r-m || r-m > MERGESORT_INPLACE_THRESHOLD)) {
		for(size_t i=l, x=0; i < m; i++, x++) {
			idx[x] = i;
			rev[i % MERGESORT_INPLACE_THRESHOLD] = x;
		}

		for(size_t i=l, j=m, x=0; i < j; i++) {
			if(j >= r || A[idx[x]] <= A[j]) {
				// use left item
				if(idx[x] != i) {
					// left item not already in place
					size_t y = rev[i % MERGESORT_INPLACE_THRESHOLD];

					A.swap(i, idx[x]);
					std::swap(idx[x], idx[y]);
					rev[idx[y] % MERGESORT_INPLACE_THRESHOLD] = y;
				}

				A.mark(i, 4);	// left item

				x++;
			} else {
				// use right item, which must displace a left item
				size_t y = rev[i % MERGESORT_INPLACE_THRESHOLD];

				A.swap(i,j);
				A.mark(i, 11);	// right item
				A.mark(j, 12);	// internally buffered left item

				idx[y] = j;
				rev[j % MERGESORT_INPLACE_THRESHOLD] = y;

				j++;
			}
		}
	} else {
		for(size_t i=r, x=0; i > m; i--, x++) {
			idx[x] = i-1;
			rev[(i-1) % MERGESORT_INPLACE_THRESHOLD] = x;
		}

		for(size_t i=r, j=m, x=0; i > j; i--) {
			if(j <= l || A[idx[x]] >= A[j-1]) {
				// use right item
				if(idx[x] != i-1) {
					// right item not already in place
					size_t y = rev[(i-1) % MERGESORT_INPLACE_THRESHOLD];

					A.swap(i-1, idx[x]);
					std::swap(idx[x], idx[y]);
					rev[idx[y] % MERGESORT_INPLACE_THRESHOLD] = y;
				}

				A.mark(i-1, 11);	// right item

				x++;
			} else {
				// use left item, which must displace a right item
				size_t y = rev[(i-1) % MERGESORT_INPLACE_THRESHOLD];

				A.swap(i-1, j-1);
				A.mark(i-1, 4); 	// left item
				A.mark(j-1, 12);	// internally buffered right item

				idx[y] = j-1;
				rev[(j-1) % MERGESORT_INPLACE_THRESHOLD] = y;

				j--;
			}
		}
	}
}

typedef enum {
	SMALL_NONE = 0,
	SMALL_MERGE
} SmallOpt;

void MergeSortMergeInPlace(SortArray& A, const size_t l, const size_t m, const size_t r, const SmallOpt smallOpt, const bool root=false)
{
	// We have two sorted blocks in [l..m) and [m..r), which we must merge into a single sorted block in [l..r).
	// First, deal with trivial cases:

	// Either of the blocks is zero-length?
	if(m <= l || r <= m)
		return;

	if(root) {
		for(size_t i=l; i < m; i++)
			A.mark(i, 4);
		for(size_t i=m; i < r; i++)
			A.mark(i, 11);
	}

	// Elements already in correct order?
	if(A[m-1] <= A[m])
		return;

	// Single-element blocks in wrong order?
	if(r-l == 2) {
		A.swap(l,m);
		A.mark_swap(l,m);
		return;
	}

	// Entire blocks need swapping?
	if(A[r-1] < A[l]) {
		A.rotate(l, m, r);
		return;
	}

	// Proceed by swapping the end of the left block with the beginning of the right block, preserving order,
	// with the lengths of the swapped blocks chosen so that after the swap, all elements on the left sort before
	// all elements on the right.  The swapped blocks need not be of equal length.
	// We use a binary search to efficiently determine these lengths, comparing mirrored pairs of elements.

	size_t x1=l, y1=m-1, z1=(x1+y1)/2;
	size_t x2=m, y2=r-1, z2=(x2+y2)/2;
	size_t mm=m;

	if(m-l < r-m) {
		// left side smaller
		y2 = (m*2-l)-1;
		z2 = (x2+y2)/2;
	} else if(m-l > r-m) {
		// right side smaller
		x1 = m*2-r;
		z1 = (x1+y1)/2;
	}

	if(m-l == r-m || A[x1] <= A[y2]) {
		// blocks of equal length, or split point is within symmetric search
		z2 = (m*2-1) - z1;

		while(x1 < y1) {
			if(A[z1] <= A[z2])
				x1 = z1 + 1;
			else
				y1 = z1;
			z1 = (x1+y1)/2;
			z2 = (m*2-1) - z1;
		}
		z2++;
	} else if(m-l > r-m) {
		// search left side for far edge of right side
		y1 = x1;
		x1 = l;
		z1 = (x1+y1)/2;
		z2 = r-1;

		while(x1 < y1) {
			if(A[z1] <= A[z2])
				x1 = z1 + 1;
			else
				y1 = z1;
			z1 = (x1+y1)/2;
		}
		z2++;
		mm = z1 + (z2 - m);
	} else {
		// search right side for far edge of left side
		x2 = y2;
		y2 = r-1;
		z2 = (x2+y2)/2;
		z1 = l;

		while(x2 < y2) {
			if(A[z1] <= A[z2])
				y2 = z2 - 1;
			else
				x2 = z2;
			z2 = (x2+y2+1)/2;
		}
		z2++;
		mm = z1 + (z2 - m);
	}
	A.rotate(z1, m, z2);

	// This yields four smaller sorted blocks (of which up to two may be zero length).
	// Recursively merge the two pairs of blocks.
	// This recursion is what makes this algorithm O(N * (log N)^2) instead of O(N log N).
	if(z1 > l) {
		if(smallOpt && mm-l < 4*MERGESORT_INPLACE_THRESHOLD
			&& (z1-l <= MERGESORT_INPLACE_THRESHOLD || mm-z1 <= MERGESORT_INPLACE_THRESHOLD))
			MergeSortMergeSmall(A, l, z1, mm);
		else
			MergeSortMergeInPlace(A, l, z1, mm, smallOpt);
	}
	if(z2 < r) {
		if(smallOpt && r-mm < 4*MERGESORT_INPLACE_THRESHOLD
			&& (z2-mm <= MERGESORT_INPLACE_THRESHOLD || r-z2 <= MERGESORT_INPLACE_THRESHOLD))
			MergeSortMergeSmall(A, mm, z2, r);
		else
			MergeSortMergeInPlace(A, mm, z2, r, smallOpt);
	}
}

void MergeSortInPlace(SortArray& A, const size_t l, const size_t r, const SmallOpt smallOpt)
{
	// Iterative mergesort.
	for(size_t s=1; s && s < (r-l); s *= 2) {
		for(size_t i=l; i < r; i += s*2) {
			size_t j=i+s;
			size_t k=j+s;

			if(j >= r)
				break;
			if(k > r)
				k = r;

			if(smallOpt == SMALL_MERGE && k-j <= MERGESORT_INPLACE_THRESHOLD)
				MergeSortMergeSmall(A, i, j, k, true);
			else
				MergeSortMergeInPlace(A, i, j, k, smallOpt, true);
		}
	}
}

// This version is truly in-place, using no temporary arrays.
void MergeSortInPlace(SortArray& A)
{
	MergeSortInPlace(A, 0, A.size(), SMALL_NONE);
}

// This version switches to a conventional mergesort for small merges, using O(1) extra memory.
void MergeSortSemiInPlace(SortArray& A)
{
	MergeSortInPlace(A, 0, A.size(), SMALL_MERGE);
}

// ****************************************************************************
// *** CataMerge Sort
//
// An adaptive, optionally stable, in-place mergesort variant.  The array is examined for
// increasing and decreasing runs of values.  Decreasing runs are reversed to make them
// increasing runs.  A list of runs is kept; whenever the last run is bigger than the
// previous one (or the end of the array is reached), the two adjacent runs with the
// smallest combined size are merged in-place.  The sort is complete when there is only
// one run left.
//
// Inspired by the abandoned "Catasort" algorithm:  https://www.youtube.com/watch?v=ND6sC_ZzUHM
// According to the author, this name is a contraction of "Catapillar sort".
//
// As far as I can tell, Catasort repeatedly identifies decreasing runs and reverses
// them, making it a sort of generalised pancake sort.  In practice the performance and
// behaviour are similar to bubble or cocktail sort, except when the whole array is in
// descending order.  By combining this idea with mergesort, considerably better behaviour
// results in the general case.

void CataMergeRuns(SortArray& A, std::vector<size_t>& runs, SmallOpt smallOpt)
{
	// find the adjacent pair of runs with the smallest total length, and merge them.
	size_t minlen=A.size(), mini=0;

	for(size_t i=0; i < runs.size()-2; i++) {
		size_t len = runs[i+2] - runs[i];
		if(len < minlen) {
			minlen = len;
			mini = i;
		}
	}

	size_t l = runs[mini], k = runs[mini+1], j = runs[mini+2];

	if(smallOpt == SMALL_MERGE) {
		if(k-l > MERGESORT_INPLACE_THRESHOLD && j-k > MERGESORT_INPLACE_THRESHOLD)
			MergeSortMergeInPlace(A, l, k, j, smallOpt, true);
		else
			MergeSortMergeSmall(A, l, k, j, true);
	} else {
		MergeSortMergeInPlace(A, l, k, j, smallOpt, true);
	}

	runs.erase(runs.begin() + mini+1);
}

void CataMergeSort(SortArray& A, bool stable, SmallOpt smallOpt = SMALL_MERGE)
{
	std::vector<size_t> runs;
	size_t i=0, j=0;
	int runPolarity = 0;

	runs.push_back(0);

	while(++j < A.size()) {
		int c = 0;

		if(stable)
			c = (A[j] < A[j-1]) ? -1 : 1;
		else
			c = A[j].cmp(A[j-1]);

		if(!runPolarity) {
			runPolarity = c;
		} else if(c * runPolarity < 0) {
			// found end of run at A[j-1]
			if(runPolarity < 0) {
				// descending run, need to reverse it
				for(size_t k=j-1; k > i; k--,i++)
					A.swap(i,k);
			}

			// record new run
			runs.push_back(j);
			runPolarity = 0;

			// check if we need to merge with previous run(s)
			for(;;) {
				// are there at least two runs?
				if(runs.size() < 3)
					break;

				size_t k = runs[runs.size()-2], l = runs[runs.size()-3];
				size_t kk = j-k, ll = k-l, mm = A.size()-j;

				// is the last run at least as big as the previous one?
				if(kk < ll || mm < kk)
					break;

				// both true, so merge required; repeat as necessary
				CataMergeRuns(A, runs, smallOpt);
			}

			i = j;
		}
	}

	// handle final run
	if(runPolarity < 0) {
		// descending run, need to reverse it
		for(size_t k=j-1; k > i; k--,i++)
			A.swap(i,k);
	}
	runs.push_back(j);

	// merge all runs found into one
	while(runs.size() > 2)
		CataMergeRuns(A, runs, smallOpt);
}

void CataMergeSort(SortArray& A)
{
	CataMergeSort(A, false);
}

void CataMergeSortStable(SortArray& A)
{
	CataMergeSort(A, true);
}

void SplayMergeSort(SortArray& A)
{
	std::vector<size_t> runs = Splay::runs(A);

	while(runs.size() > 2)
		CataMergeRuns(A, runs, SMALL_MERGE);
}

