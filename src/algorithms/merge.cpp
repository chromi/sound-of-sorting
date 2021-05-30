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
		A.swap(l, m, true);
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


#include "algorithms/heap.h"

void SplayMergeSort(SortArray& A)
{
	std::vector<size_t> runs = SplayCollectRuns(A);

	while(runs.size() > 2)
		CataMergeRuns(A, runs, SMALL_MERGE);
}



// ****************************************************************************
// *** Adaptive Bitonic Merge Sort
// *** by Jonathan Morton
//
// An adaptive, stable, in-place mergesort variant based on the bitonic principle.
//
// A bitonic sequence is one that can be cylindrically rotated to consist of a
// monotonically increasing sequence followed by a monotonically decreasing sequence.
// A monotonic sequence, either ascending or descending, is a degenerate case of a
// bitonic sequence.  Any arbitrary sequence of up to three values is also a bitonic
// sequence.
//
// A bitonic sequence can be sorted into a monotonically ascending sequence using a
// recursive "bitonic rectify" algorithm.  Two adjacent monotonically ascending
// sequences can be converted into a pair of bitonic sequences by a "bitonic
// partition" algorithm which ensures that all elements in the right sequence are
// greater than or equal to all elements in the left sequence.
//
// Combining these "bitonic partition" and "bitonic rectify" procedures merges the
// two original sequences into a single monotonically increasing sequence.  The
// combination can thus be used as a standard in-place merge step in a variety of
// mergesort algorithms.
//
// These are the essential principles behind the well-known Bitonic Sorting Network
// published long ago by Batcher.  The Adaptive Bitonic Merge Sort optimises this
// procedure by exploiting certain regular features of the bitonic partition and rectify
// steps, which reduce the number of comparisons that need to be made (by conducting
// binary rather than linear searches) and also enable stable sorting.  To facilitate
// this, information about the locations of the ascending and descending sequences is
// passed through the recursion.
//
// Additionally, an unsorted array can be searched for already existing bitonic
// sequences, which can then be rectified and used as seed runs for a merge tree.
// This requires treating runs of equal values as forming a monotonically ascending
// sequence.

// Convert a bitonic sequence into an ascending sequence.
// This is done by recursively partitioning the bitonic sequence by its median.
// This "dumb" version does a full-width binary search without tracking ascending/descending subsequences.
void BitonicDumbRectify(SortArray& A, const size_t l, const size_t r)
{
	const size_t len = r - l;

	if(r <= l)
		return;

	if(len < 2)
		return;
	if(len == 2) {
		if(A[l] > A[l+1])
			A.swap(l, l+1, true);
		return;
	}

	const size_t half = len / 2, mirror = len - half;
	const bool rectLeft  = (A[l] > A[l + mirror]);
	const bool rectRight = (A[(r-1) - mirror] > A[r-1]);

	if(!rectLeft && !rectRight) {
		// no swaps here, just recurse
		BitonicDumbRectify(A, l, l + mirror);
		BitonicDumbRectify(A, l + half, r);
	} else if(rectLeft && rectRight) {
		// swap them all, then recurse
		for(size_t i = l, j = l + mirror; j < r; i++, j++)
			A.swap(i, j, true);
		BitonicDumbRectify(A, l, l + mirror);
		BitonicDumbRectify(A, l + half, r);
	} else if(rectLeft && !rectRight) {
		// find split point so we can swap A-B-C-D to C-B-A-D, keeping middle element with left
		size_t leftEdge = l + 1;			// just after last element known in wrong order
		size_t rightEdge = l + half - 1;	// first element known in right order

		while(leftEdge < rightEdge) {
			size_t mid = leftEdge + (rightEdge - leftEdge) / 2;
			if(A[mid] > A[mid + mirror])
				leftEdge = mid+1;
			else
				rightEdge = mid;
		}

		// swap A elements with their C mirrors, left of leftEdge
		for(size_t i = l; i < leftEdge; i++)
			A.swap(i, i + mirror, true);

		BitonicDumbRectify(A, l, l + mirror);
		BitonicDumbRectify(A, l + mirror, r);
	} else if(!rectLeft && rectRight) {
		// find split point so we can swap A-B-C-D to A-D-C-B, keeping middle element with right
		size_t leftEdge = l + 1;			// just after last element known in right order
		size_t rightEdge = l + half - 1;	// first element known in wrong order

		while(leftEdge < rightEdge) {
			size_t mid = leftEdge + (rightEdge - leftEdge) / 2;
			if(A[mid] > A[mid + mirror])
				rightEdge = mid;
			else
				leftEdge = mid+1;
		}

		// swap B elements with their D mirrors, from rightEdge rightwards
		for(size_t i = rightEdge; i < l + half; i++)
			A.swap(i, i + mirror, true);

		BitonicDumbRectify(A, l, l + half);
		BitonicDumbRectify(A, l + half, r);
	}

	// DEBUG
	// check whether the block was properly rectified
	for(size_t i=l+1; i < r; i++) {
		if(A[i] < A[i-1]) {
			fprintf(stderr, "bad output from BitonicDumbRectify(%lu,%lu): %s %s\n", l, r, rectLeft ? "rectLeft" : "!rectLeft", rectRight ? "rectRight" : "!rectRight");
			SplaySort(A, l, r);
			break;
		}
	}
}

// Merge two adjacent ascending sequences by bitonic partition and rectify.
// This version calls the "dumb" rectify and does not result in a stable sort.
void BitonicDumbPartition(SortArray& A, const size_t l, const size_t m, const size_t r)
{
	const size_t lenL = m - l, lenR = r - m;

	if(l >= m || m >= r)
		return;

	// mark left and right sequences visually
	for(size_t i=l; i < m; i++)
		A.mark(i, 4);
	for(size_t i=m; i < r; i++)
		A.mark(i, 11);

	// deal with the easy cases
	if(lenL == 1 && lenR == 1) {
		// simple compare and swap
		if(A[l] > A[m])
			A.swap(l, m, true);
		return;
	}
	if(A[m] >= A[m-1])
		return;		// already in correct order
	if(A[l] > A[r-1]) {
		// swap entire blocks
		A.rotate(l,m,r);
		return;
	}

	// insert single-element blocks directly
	// compares have already occurred with first and last elements in longer run
	if(lenL == 1) {
		size_t leftEdge = m+1;
		size_t rightEdge = r-1;
		const value_type v = A[l];

		while(leftEdge < rightEdge) {
			size_t mid = leftEdge + (rightEdge - leftEdge) / 2;
			if(v > A[mid])
				leftEdge = mid+1;
			else
				rightEdge = mid;
		}

		A.rotate(l, m, leftEdge);
		return;
	} else if(lenR == 1) {
		size_t leftEdge = l+1;
		size_t rightEdge = m-1;
		const value_type v = A[m];

		while(leftEdge < rightEdge) {
			size_t mid = leftEdge + (rightEdge - leftEdge) / 2;
			if(v < A[mid])
				rightEdge = mid;
			else
				leftEdge = mid+1;
		}

		A.rotate(rightEdge, m, r);
		return;
	}

	// convert two ascending runs into two bitonic runs, partitioned by a median pivot
	// we search for a median position in each run in turn, then reverse the block between them
	// first search the right partition for a split point based on the left median
	// then search the left partition for a split point based on the right split point
	size_t leftEdge = m, rightEdge = r;

	const size_t midL = l + lenL / 2;
	const value_type vL = A[midL];

	while(leftEdge < rightEdge) {
		size_t mid = leftEdge + (rightEdge - leftEdge) / 2;
		if(vL > A[mid])
			leftEdge = mid+1;
		else
			rightEdge = mid;
	}

	const size_t midR = rightEdge == r ? r-1 : rightEdge;	// first element in right block that's >= left median element
	const value_type vR = A[midR];

	leftEdge = midL + 1;
	rightEdge = m;

	while(leftEdge < rightEdge) {
		size_t mid = leftEdge + (rightEdge - leftEdge) / 2;
		if(A[mid] > vR)
			rightEdge = mid;
		else
			leftEdge = mid+1;
	}

	// perform the reversal, and calculate the new division between the two sequences
	const size_t revL = leftEdge, revR = midR;
	const size_t newMid = revL + (revR - m);

	A.reverse(revL, revR);

	// rectify both bitonic sequences
	BitonicDumbRectify(A, l, newMid);
	BitonicDumbRectify(A, newMid, r);
}


// Driver routines for bitonic merging
void BitonicMergeRecursive(SortArray& A, const size_t l, const size_t r)
{
	if(r-l < 2)
		return;

	const size_t m = (l+r)/2;

	BitonicMergeRecursive(A, l, m);
	BitonicMergeRecursive(A, m, r);

	BitonicDumbPartition(A, l, m, r);
}

void BitonicMergeRecursive(SortArray& A)
{
	BitonicMergeRecursive(A, 0, A.size());
}

void BitonicMergeIterative(SortArray& A)
{
	for(size_t p=1; p < A.size(); p *= 2)
		for(size_t i=0; i+p < A.size(); i += p*2)
			BitonicDumbPartition(A, i, i+p, std::min(i+p+p, A.size()));
}

void BitonicCataMergeRuns(SortArray& A, std::vector<size_t>& runs)
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

	// use the in-place bitonic merge step
	BitonicDumbPartition(A, l, k, j);

	runs.erase(runs.begin() + mini+1);
}

void BitonicCataMerge(SortArray& A)
{
	std::vector<size_t> runs;
	size_t i=0, j=0;

	runs.push_back(0);

	while(++j < A.size()) {
		const value_type iv = A[i];

		if(A[j] >= iv) {
			// gather bitonic sequence starting with ascending subsequence
			do {
				j++;	// find extent of ascending run
			} while(j < A.size() && A[j] >= A[j-1]);

			const size_t k = j;		// start of descending run

			while(j < A.size() && A[j] < A[j-1])
				j++;	// find extent of descending run

			const size_t l = j;		// end of descending run

			while(j < A.size() && A[j] <= iv && A[j] >= A[j-1])
				j++;	// an ascending run leading to at most the initial value

			if(j > k) {
				// rectify the bitonic sequence into an ascending one
				BitonicDumbRectify(A, i, j);
			}
		} else {
			// gather bitonic sequence starting with descending subsequence
			do {
				j++;	// find extent of descending run
			} while(j < A.size() && A[j] < A[j-1]);

			const size_t k = j;		// start of ascending run

			while(j < A.size() && A[j] >= A[j-1])
				j++;	// find extent of ascending run

			const size_t l = j;		// end of ascending run

			while(j < A.size() && A[j] > iv && A[j] < A[j-1])
				j++;	// a descending run terminating before the initial value

			if(j > k) {
				// rectify the bitonic sequence into an ascending one
				BitonicDumbRectify(A, i, j);
			} else {
				// it's a descending only sequence, just reverse it
				A.reverse(i, j);
			}
		}

		// add the run to the list
		runs.push_back(j);

		// check if we need to consolidate early
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
			BitonicCataMergeRuns(A, runs);
		}

		i = j;
	}

	if(runs.back() < A.size())
		runs.push_back(A.size());

	while(runs.size() > 2)
		BitonicCataMergeRuns(A, runs);
}

void BitonicSplayMerge(SortArray& A)
{
	std::vector<size_t> runs = SplayCollectRuns(A);

	while(runs.size() > 2)
		BitonicCataMergeRuns(A, runs);
}

#if 0

// Convert a bitonic sequence into an ascending sequence.
// This is done by recursively partitioning the bitonic sequence by its median.
// This "smart" version tracks ascending and descending subsequences, searches only
// ranges that can cross, and puts equal elements in correct order.
void BitonicRectify(SortArray& A, const size_t l, const size_t r, const size_t aOff, const size_t aLen)
{
	const size_t len = r - l;

	ASSERT(r > l);
	ASSERT(aLen <= len);
	ASSERT(aOff < len);

	if(aLen == len) {
		// fully ascending sequence, just need to rotate it into position
		if(aOff)
			A.rotate(l, aOff, r);
		return;
	} else if(!aLen) {
		// fully descending sequence, just need to reverse and rotate
		if(aOff)
			A.rotate(l, aOff, r);
		A.reverse(l, r);
		return;
	}

	// The basic bitonic rectify is floor(N/2) compare-swaps between "mirrored" items i and i+ceil(N/2).
	// This always results in an initial A-B-C-D series of blocks being rearranged to either
	// C-B-A-D or A-D-C-B, where the swapped pair of blocks are of equal length.  The split
	// point between A-B and C-D is always in a range where the mirrored items are in runs of
	// opposite direction.  Hence we only need to search the shorter run, and we can do so
	// with a binary search.  The shorter run can never straddle *both* the end of the
	// sequence and the halfway mark, only one or the other.
	// Note that to handle odd-length sequences, there may be one element in the middle that
	// is never searched, but is passed down as part of whichever adjacent block doesn't move.
	const size_t dOff = (aOff + aLen) > len ? aOff + aLen - len : aOff + aLen;
	const size_t dLen = len - aLen;
	const size_t half = len / 2, mirror = len - half;
	size_t leftEdge, rightEdge;
	bool searchFromRight;  // distinguishes C-B-A-D from A-D-C-B.

	if(aLen < mirror) {
		// we'll search the ascending run
		if(aOff < half && (aOff + aLen < half || A[l] <= A[l + mirror])) {
			// relevant part of ascending run is in left half of mirror
			leftEdge = l + aOff;
			rightEdge = l + ((aOff + aLen < half) ? aOff + aLen : half);
			searchFromRight = true;
		} else if(aOff < half) {
			// ascending run straddles halfway mark, and relevant part is in right half of mirror
			leftEdge = l;
			rightEdge = l + aOff + aLen - mirror;
			searchFromRight = false;
		} else if(aOff + aLen <= len || A[l] <= A[l + mirror]) {
			// relevant part of ascending run is in right half of mirror
			leftEdge = (aOff < mirror) ? l : l + aOff - mirror;
			rightEdge = (aOff + aLen < len) ? l + aOff + aLen - mirror : half;
			searchFromRight = false;
		} else {
			// ascending run straddles beginning/end, and relevant part is in left half of mirror
			leftEdge = l;
			rightEdge = l + aOff + aLen - len;
			searchFromRight = true;
		}
	} else {
		// we'll search the descending run
		if(dOff < half && (dOff + dLen < half || A[l] > A[l + mirror])) {
			// relevant part of descending run is in left half of mirror
			leftEdge = l + dOff;
			rightEdge = l + ((dOff + dLen < half) ? dOff + dLen : half);
			searchFromRight = false;
		} else if(dOff < half) {
			// descending run straddles halfway mark, and relevant part is in right half of mirror
			leftEdge = l;
			rightEdge = l + dOff + dLen - mirror;
			searchFromRight = true;
		} else if(dOff + dLen <= len || A[l] > A[l + mirror]) {
			// relevant part of descending run is in right half of mirror
			leftEdge = (dOff < mirror) ? l : l + dOff - mirror;
			rightEdge = (dOff + dLen < len) ? l + dOff + dLen - mirror : half;
			searchFromRight = true;
		} else {
			// descending run straddles beginning/end, and relevant part is in left half of mirror
			leftEdge = l;
			rightEdge = l + dOff + dLen - len;
			searchFromRight = false;
		}
	}

	// Search the selected half-open interval for the A-B split point, then resolve it.
	if(searchFromRight) {
		// we'll swap B with D, resulting in A-D-C-B order, middle element stays with C
		const size_t aOffLeft  = (aOff < half) ? aOff : (aOff == half) ? 0 : aOff - mirror;
		const size_t dOffLeft  = (dOff < half) ? dOff : (dOff == half) ? 0 : dOff - mirror;
		const size_t aOffRight = (aOff < half) ? aOff + mirror - half : aOff - half;
		const size_t dOffRight = (dOff < half) ? dOff + mirror - half : dOff - half;

		// rightEdge indicates the first element known to be in the wrong order
		// leftEdge is just after the last element known to be in the right order
		while(leftEdge < rightEdge) {
			size_t mid = leftEdge + (rightEdge - leftEdge) / 2;
			if(A[mid] > A[mid + mirror])
				rightEdge = mid;
			else
				leftEdge = mid+1;
		}

		// swap B elements with their D mirrors, from rightEdge rightwards
		for(size_t i = rightEdge; i < l + half; i++)
			A.swap(i, i + mirror, true);

		// enumerate components of A, B, C, D blocks
		const size_t lenA = rightEdge - l;
		const size_t lenB = half - lenA, lenD = lenB;
		const size_t lenC = mirror - lenD;
		const size_t aOffA = (aOff < lenA) ? aOff : 0;
		const size_t aLenA = (aOff < lenA) ? (aOff + aLen <= lenA ? aLen : lenA - aOff) : 0;

		// recurse to rectify left half
		size_t aOffLeft = (aOff == half) ? 0 : (aOff < half) ? aOff : aOff - mirror;
		size_t aLenLeft = (aOffLeft <= rightEdge) ? rightEdge - aOffLeft : rightEdge + half - aOffLeft;
		if(!aLenLeft && )
		BitonicRectify(A, l, half, aOffLeft, aLenLeft);

		// recurse to rectify right half, including middle element


	} else {
		// rightEdge indicates the first element known to be in the right order
		// leftEdge is just after the last element known to be in the wrong order
		while(leftEdge < rightEdge) {
			size_t mid = leftEdge + (rightEdge - leftEdge) / 2;
			if(A[mid] >= A[mid + mirror])
				leftEdge = mid+1;
			else
				rightEdge = mid;
		}

		// swap A elements with their C mirrors, leftwards beyond leftEdge
		for(size_t i = l; i < leftEdge; i++)
			A.swap(i, i + mirror, true);

		// recurse to rectify left half, including middle element


		// recurse to rectify right half

		
	}


}

#endif
