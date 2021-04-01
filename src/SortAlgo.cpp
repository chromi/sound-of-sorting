/******************************************************************************
 * src/SortAlgo.cpp
 *
 * Implementations is many sorting algorithms.
 *
 * Note that these implementations may not be as good/fast as possible. Some
 * are modified so that the visualization is more instructive.
 *
 * Futhermore, some algorithms are annotated using the mark() and watch()
 * functions from SortArray. These functions add colors to the illustratation
 * and thereby makes the algorithm's visualization easier to explain.
 *
 ******************************************************************************
 * The algorithms in this file are copyrighted by the original authors. All
 * code is freely available.
 *
 * The source code added by myself (Timo Bingmann) and all modifications are
 * copyright (C) 2013-2014 Timo Bingmann <tb@panthema.net>
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

#include "algorithms/insertion.h"

#include <algorithm>
#include <numeric>
#include <limits>
#include <random>
#include <vector>
#include <inttypes.h>

typedef ArrayItem value_type;

// inversion count limit for iterator instrumented algorithms
const unsigned int inversion_count_instrumented = 512;

const struct AlgoEntry g_algolist[] =
{
	{ _("Selection Sort"), &SelectionSort, 10240, UINT_MAX,
	wxEmptyString },
	{ _("Dual Selection Sort"), &DualSelectionSort, 10240, UINT_MAX,
	wxEmptyString },

	{ _("Insertion Sort"), &InsertionSort, 10240, UINT_MAX,
	wxEmptyString },
	{ _("Binary Insertion Sort"), &BinaryInsertionSort, 10240, UINT_MAX,
	wxEmptyString },

	{ _("Shell Sort (Shell 1959)"), &ShellSort_Shell59,
	UINT_MAX, UINT_MAX, _("Gap sequence: N/2, N/4, ...") },
	{ _("Shell Sort (Frank 1960)"), &ShellSort_Frank60,
	UINT_MAX, UINT_MAX, _("Gap sequence: N/2+1, N/4+1, ...") },
	{ _("Shell Sort (Hibbard 1963)"), &ShellSort_Hibbard63,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 3, 7, 15, 31, 63, ...\n2^k - 1") },
	{ _("Shell Sort (Papernov 1965)"), &ShellSort_Papernov65,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 3, 5, 9, 17, 33, 65, ...\n2^k + 1") },
	{ _("Shell Sort (Pratt 1971)"), &ShellSort_Pratt71,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 2, 3, 4, 6, 8, 9, 12, ...\n(2^p)*(3^q)") },
	{ _("Shell Sort (Knuth 1973)"), &ShellSort_Knuth73,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 4, 13, 40, 121, 364, 1093, 3280, ...\n(3^k - 1) / 2") },
	{ _("Shell Sort (Sedgewick 1982)"), &ShellSort_Sedgewick82,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 8, 23, 77, 281, 1073, 4193, ...\n4^k + 3*2^(k-1) + 1") },
	{ _("Shell Sort (Incerpi-Sedgewick 1985)"), &ShellSort_Incerpi85,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 3, 7, 21, 48, 112, 336, 861, 1968, ...") },
	{ _("Shell Sort (Sedgewick 1986)"), &ShellSort_Sedgewick86,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 5, 19, 41, 109, 209, 505, 929, 2161, 3905, ...\nEven k: 9*(2^k - 2^(k/2)) + 1\nOdd k: 8*2^k - 6*2^((k+1)/2) + 1") },
	{ _("Shell Sort (Gonnet 1991)"), &ShellSort_Gonnet91,
	UINT_MAX, UINT_MAX, _("Gap sequence: floor(N * 5/11), ...") },
	{ _("Shell Sort (Tokuda 1992)"), &ShellSort_Tokuda92,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 4, 9, 20, 46, 103, 233, 525, 1182, 2660, ...\nf(k)=f(k-1)*2.25+1 | ceil(f(k))") },
	{ _("Shell Sort (Ciura 2001)"), &ShellSort_Ciura2001,
	65536,    UINT_MAX, _("Gap sequence: 1, 4, 10, 23, 57, 132, 301, 701") },
	{ _("Shell Sort (Ciura-Tokuda)"), &ShellSort_CiuraTokuda,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 4, 10, 23, 57, 132, 301, 701, 1579, 3553, ...\nCiura sequence extended by Tokuda formula") },
	{ _("Shell Sort (Ciura-Pratt)"), &ShellSort_CiuraPratt,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 4, 10, 23, 57, 132, 301, 701, 1311, 3249, ...\nCiura sequence extended with Pratt-type (23^p)*(57^q) sequence") },
	{ _("Shell Sort (Ciura-Fibonacci)"), &ShellSort_CiuraFibonacci,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 4, 10, 23, 57, 132, 301, 701, 1002, 1703, 2705, ...\nCiura sequence extended with Fibonacci sequence") },
	{ _("Shell Sort (Ciura-Fibonacci squared)"), &ShellSort_CiuraFibonacci2,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 4, 10, 23, 57, 132, 301, 701, 1849, 4761, ...\nCiura sequence extended with squared Fibonacci sequence") },
	{ _("Shell Sort (Ciura-Fibonacci cubed)"), &ShellSort_CiuraFibonacci3,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 4, 10, 23, 57, 132, 301, 701, 4096, ...\nCiura sequence extended with cubed Fibonacci sequence") },
	{ _("Shell Sort (Ciura, sqrt(5) coprime)"), &ShellSort_CiuraRoot5,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 4, 10, 23, 57, 132, 301, 701, 1567, 3503, ...\nCiura sequence extended with coprime sequence") },
	{ _("Shell Sort (sqrt(5) coprime)"), &ShellSort_Root5_Coprime,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 5, 11, 24, 53, 119, 269, 601, 1339, 2993, ...\nratio approx sqrt(5), gaps mutually coprime") },
	{ _("Shell Sort (e coprime)"), &ShellSort_e_Coprime,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 7, 19, 52, 141, 383, 1039, 2825, ...\nratio approx e, gaps mutually coprime") },
	{ _("Shell Sort (pi coprime)"), &ShellSort_pi_Coprime,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 6, 19, 59, 185, 581, 1823, ...\nratio approx pi, gaps mutually coprime") },
	{ _("Shell Sort (Fibonacci)"), &ShellSort_Fibonacci,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, ...") },
	{ _("Shell Sort (Fibonacci squared)"), &ShellSort_FibonacciSquared,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 4, 9, 25, 64, 169, 441, 1156, 3025, ...") },
	{ _("Shell Sort (Fibonacci cubed)"), &ShellSort_FibonacciCubed,
	UINT_MAX, UINT_MAX, _("Gap sequence: 1, 8, 27, 125, 512, 2197, ...") },

	{ _("Merge Sort"), &MergeSort, UINT_MAX, UINT_MAX,
	_("Merge sort which merges two sorted sequences into a shadow array,"
		"and then copies it back to the shown array.") },
	{ _("Merge Sort (iterative)"), &MergeSortIterative, UINT_MAX, UINT_MAX,
	_("Merge sort variant which iteratively merges "
		"subarrays of sizes of powers of two.") },
	{ _("Merge Sort (in-place)"), &MergeSortInPlace, UINT_MAX, UINT_MAX,
	_("Merge sort variant which iteratively merges "
		"subarrays of sizes of powers of two, using an in-place merging algorithm.") },
	{ _("Merge Sort (semi-in-place)"), &MergeSortSemiInPlace, UINT_MAX, UINT_MAX,
	_("Merge sort variant which iteratively merges "
		"subarrays of sizes of powers of two, using a fixed amount of temporary storage.") },
	{ _("CataMerge Sort (stable)"), &CataMergeSortStable, UINT_MAX, UINT_MAX,
	_("Merge sort variant which searches for runs in either direction, reverses descending runs, then merges them.  Runs of equal values are treated as ascending.") },
	{ _("CataMerge Sort (non-stable)"), &CataMergeSort, UINT_MAX, UINT_MAX,
	_("Merge sort variant which searches for runs in either direction, reverses descending runs, then merges them.  Runs of equal values are treated as part of a run in either direction.") },
	{ _("Splay Merge Sort"), &SplayMergeSort, UINT_MAX, UINT_MAX,
	_("Merge sort variant which uses splaysort to collect ascending runs, then merges adjacent pairs of runs in-place.") },

	{ _("Quick Sort (LR ptrs)"), &QuickSortLR, 16384, UINT_MAX,
	_("Quick sort variant with left and right pointers.") },
	{ _("Quick Sort (LL ptrs)"), &QuickSortLL, 16384, UINT_MAX,
	_("Quick sort variant from 3rd edition of CLRS: two pointers on left.") },
	{ _("Quick Sort (ternary, LR ptrs)"), &QuickSortTernaryLR, 16384, UINT_MAX,
	_("Ternary-split quick sort variant, adapted from multikey quicksort by "
		"Bentley & Sedgewick: partitions \"=<?>=\" using two pairs of pointers "
		"at left and right, then copied to middle.") },
	{ _("Quick Sort (ternary, LL ptrs)"), &QuickSortTernaryLL, 16384, UINT_MAX,
	_("Ternary-split quick sort variant: partitions \"<>?=\" using two "
		"pointers at left and one at right. Afterwards copies the \"=\" to middle.") },
	{ _("Quick Sort (dual pivot)"), &QuickSortDualPivot, UINT_MAX, UINT_MAX,
	_("Dual pivot quick sort variant: partitions [ A < p <= B <= q < C ] using three pointers, "
		"two at left and one at right.") },

	{ _("IntroSort (ternary, insertion)"), &IntroSort, UINT_MAX, UINT_MAX,
	_("Ternary-split quicksort variant with the usual practical implementation features: "
		"insertion-sort of small blocks, pivot values' position established without a separate rearrangement pass, "
		"and smallest-first recursion to exploit tail-call optimisation.") },
	{ _("IntroSort (dual pivot, splaysort)"), &IntroSortDual, UINT_MAX, UINT_MAX,
	_("A version of Introsort based on dual-pivot quicksort and splaysort, choosing pivots using random sampling.") },
	{ _("Stable IntroSort (dual pivot, splaysort)"), &IntroSortDualStable, UINT_MAX, UINT_MAX,
	_("A version of Introsort based on dual-pivot quicksort and splaysort, choosing pivots using random sampling, and using stable partitioning.") },

	{ _("Septenary Quicksort"), &SeptenaryQuickSort, UINT_MAX, UINT_MAX,
	_("Septenary-split quicksort variant with three pivots (quartiles of random sample), "
		"insertion-sort of small blocks, and smallest-first partitioning with a priority queue.") },
	{ _("Septenary Stable Quicksort"), &SeptenaryStableQuickSort, UINT_MAX, UINT_MAX,
	_("Septenary-split stable quicksort variant with three pivots (quartiles of random sample), "
		"insertion-sort of small blocks, and smallest-first partitioning with a priority queue.") },

	{ _("Bubble Sort"), &BubbleSort, 10240, UINT_MAX,
	wxEmptyString },
	{ _("Cocktail Shaker Sort"), &CocktailShakerSort, 10240, UINT_MAX,
	wxEmptyString },
	{ _("Gnome Sort"), &GnomeSort, 10240, UINT_MAX,
	wxEmptyString },

	{ _("Comb Sort (1/1.3)"), &CombSort, UINT_MAX, UINT_MAX,
	wxEmptyString },
	{ _("Comb Sort (Pratt 1973)"), &CombSortPratt, UINT_MAX, UINT_MAX,
	wxEmptyString },
	{ _("Comb Sort (Fibonacci)"), &CombSortFibonacci, 250000, UINT_MAX,
	wxEmptyString },
	{ _("Groom Sort (Fibonacci)"), &GroomSort, UINT_MAX, UINT_MAX,
	wxEmptyString },

	{ _("Heap Sort"), &HeapSort, UINT_MAX, UINT_MAX,
	wxEmptyString },
	{ _("Smooth Sort"), &SmoothSort, UINT_MAX, UINT_MAX,
	wxEmptyString },
	{ _("Splay Sort"), &SplaySort, UINT_MAX, UINT_MAX,
	wxEmptyString },
	{ _("Splay Shake Sort"), &SplayShakeSort, 65536, UINT_MAX,
	wxEmptyString },

	{ _("Odd-Even Sort"), &OddEvenSort, 10240, UINT_MAX,
	wxEmptyString },
	// older sequential implementation, which really makes little sense to do
	//{ _("Bitonic Sort"), &BitonicSort, UINT_MAX, UINT_MAX, wxEmptyString },
	{ _("Batcher's Bitonic Sort"), &BitonicSortNetwork, 250000, UINT_MAX,
	wxEmptyString },
	{ _("Batcher's Odd-Even Merge Sort"), &BatcherSortNetwork, 250000, UINT_MAX,
	wxEmptyString },
	{ _("Cycle Sort"), &CycleSort, 10240, UINT_MAX,
	wxEmptyString },
	{ _("Radix Sort (LSD)"), &RadixSortLSD, UINT_MAX, UINT_MAX,
	_("Least significant digit radix sort, which copies item into a shadow "
		"array during counting.") },
	{ _("Radix Sort (MSD)"), &RadixSortMSD, UINT_MAX, UINT_MAX,
	_("Most significant digit radix sort, which permutes items in-place by walking cycles.") },
	{ _("std::sort (gcc)"), &StlSort, UINT_MAX, inversion_count_instrumented,
	wxEmptyString },
	{ _("std::stable_sort (gcc)"), &StlStableSort, UINT_MAX, inversion_count_instrumented,
	wxEmptyString },
	{ _("std::sort_heap (gcc)"), &StlHeapSort, UINT_MAX, inversion_count_instrumented,
	wxEmptyString },
	{ _("Tim Sort"), &TimSort, UINT_MAX, inversion_count_instrumented,
	wxEmptyString },
	{ _("Block Merge Sort (WikiSort)"), &WikiSort, UINT_MAX, inversion_count_instrumented,
	_("An O(1) place O(n log n) time stable merge sort.") },
//	{ _("Bogo Sort"), &BogoSort, 10, UINT_MAX,
//	wxEmptyString },
//	{ _("Bozo Sort"), &BozoSort, 10, UINT_MAX,
//	wxEmptyString },
	{ _("Stooge Sort"), &StoogeSort, 1050, inversion_count_instrumented,
	wxEmptyString },
	{ _("Slow Sort"), &SlowSort, 500, inversion_count_instrumented,
	wxEmptyString }
};

const size_t g_algolist_size = sizeof(g_algolist) / sizeof(g_algolist[0]);

const struct AlgoEntry* g_algolist_end = g_algolist + g_algolist_size;

// ****************************************************************************
// *** Selection Sort

void SelectionSort(SortArray& A)
{
	volatile ssize_t jMin = 0;
	A.watch(&jMin, 3);

	for (size_t i = 0; i < A.size()-1; ++i)
	{
		jMin = i;

		for (size_t j = i+1; j < A.size(); ++j)
		{
			if (A[j] < A[jMin]) {
				A.mark_swap(j, jMin);
				jMin = j;
			}
		}

		A.swap(i, jMin);

		// mark the last good element
		if (i > 0) A.unmark(i-1);
		A.mark(i);
	}
	A.unwatch_all();
}

void DualSelectionSort(SortArray& A)
{
	volatile ssize_t jMin = 0, jMax = 0;
	A.watch(&jMin, 3);
	A.watch(&jMax, 3);

	for (size_t i = 0; i < A.size() / 2; ++i)
	{
		size_t k = A.size() - i;
		value_type tMin, tMax;
		jMin = jMax = i;
		tMin = tMax = A[i];

		for (size_t j = i+1; j < k; ++j)
		{
			const value_type t = A[j];

			if (t < tMin) {
				A.mark_swap(j, jMin);
				jMin = j;
				tMin = t;
			} else if (t > tMax) {
				A.mark_swap(j, jMax);
				jMax = j;
				tMax = t;
			}
		}

		A.swap(i, jMin);
		if(jMax == (ssize_t) i)
			jMax = jMin;
		A.swap(k-1, jMax);

		// mark the last good element
		A.mark(i);
		A.mark(k-1);
	}
	A.unwatch_all();
}

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

// ****************************************************************************
// *** Odd-Even Sort

// from http://en.wikipediA.org/wiki/Odd%E2%80%93even_sort

void OddEvenSort(SortArray& A)
{
	bool sorted = false;

	while (!sorted)
	{
		sorted = true;

		for (size_t i = 1; i < A.size()-1; i += 2)
		{
			if(A[i] > A[i+1])
			{
				A.swap(i, i+1);
				sorted = false;
			}
		}

		for (size_t i = 0; i < A.size()-1; i += 2)
		{
			if(A[i] > A[i+1])
			{
				A.swap(i, i+1);
				sorted = false;
			}
		}
	}
}

// ****************************************************************************
// *** Heap Sort

// heavily adapted from http://www.codecodex.com/wiki/Heapsort

bool isPowerOfTwo(size_t x)
{
	return ((x != 0) && !(x & (x - 1)));
}

uint32_t prevPowerOfTwo(uint32_t x)
{
	x |= x >> 1; x |= x >> 2; x |= x >> 4;
	x |= x >> 8; x |= x >> 16;
	return x - (x >> 1);
}

int largestPowerOfTwoLessThan(int n)
{
	int k = 1;
	while (k < n) k = k << 1;
	return k >> 1;
}

void HeapSort(SortArray& A)
{
	size_t n = A.size(), i = n / 2;

	// mark heap levels with different colors
	for (size_t j = i; j < n; ++j)
		A.mark(j, log(prevPowerOfTwo(j+1)) / log(2) + 4);

	while (1)
	{
		if (i > 0) {
			// build heap, sift A[i] down the heap
			i--;
		}
		else {
			// pop largest element from heap: swap front to back, and sift
			// front A[0] down the heap
			n--;
			if (n == 0) return;
			A.swap(0,n);

			A.mark(n);
			if (n+1 < A.size()) A.unmark(n+1);
		}

		size_t parent = i;
		size_t child = i*2 + 1;

		// sift operation - push the value of A[i] down the heap
		while (child < n)
		{
			if (child + 1 < n && A[child + 1] > A[child]) {
				child++;
			}
			if (A[child] > A[parent]) {
				A.swap(parent, child);
				parent = child;
				child = parent*2+1;
			}
			else {
				break;
			}
		}

		// mark heap levels with different colors
		A.mark(i, log(prevPowerOfTwo(i+1)) / log(2) + 4);
	}

}

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

// ****************************************************************************
// *** Use STL Sorts via Iterator Adapters

void StlSort(SortArray& A)
{
	std::sort(MyIterator(&A,0), MyIterator(&A,A.size()));
}

void StlStableSort(SortArray& A)
{
	std::stable_sort(MyIterator(&A,0), MyIterator(&A,A.size()));
}

void StlHeapSort(SortArray& A)
{
	std::make_heap(MyIterator(&A,0), MyIterator(&A,A.size()));
	std::sort_heap(MyIterator(&A,0), MyIterator(&A,A.size()));
}

// ****************************************************************************
// *** BogoSort and more slow sorts

// by myself (Timo Bingmann)

bool BogoCheckSorted(SortArray& A)
{
	size_t i;
	value_type prev = A[0];
	A.mark(0);
	for (i = 1; i < A.size(); ++i)
	{
		value_type val = A[i];
		if (prev > val) break;
		prev = val;
		A.mark(i);
	}

	if (i == A.size()) {
		// this is amazing.
		return true;
	}

	// unmark
	while (i > 0) A.unmark(i--);
	A.unmark(0);

	return false;
}

void BogoSort(SortArray& A)
{
	// keep a permutation of [0,size)
	std::vector<size_t> perm(A.size());

	for (size_t i = 0; i < A.size(); ++i)
		perm[i] = i;

	while (1)
	{
		// check if array is sorted
		if (BogoCheckSorted(A)) break;

		// pick a random permutation of indexes
		std::random_shuffle(perm.begin(), perm.end());

		// permute array in-place
		std::vector<char> pmark(A.size(), 0);

		for (size_t i = 0; i < A.size(); ++i)
		{
			if (pmark[i]) continue;

			// walk a cycle
			size_t j = i;

			//std::cout << "cycle start " << j << " -> " << perm[j] << "\n";

			while ( perm[j] != i )
			{
				ASSERT(!pmark[j]);
				A.swap(j, perm[j]);
				pmark[j] = 1;

				j = perm[j];
				//std::cout << "cycle step " << j << " -> " << perm[j] << "\n";
			}
			//std::cout << "cycle end\n";

			ASSERT(!pmark[j]);
			pmark[j] = 1;
		}

		//std::cout << "permute end\n";

		for (size_t i = 0; i < A.size(); ++i)
			ASSERT(pmark[i]);
	}
}

void BozoSort(SortArray& A)
{
	srand(time(NULL));

	while (1)
	{
		// check if array is sorted
		if (BogoCheckSorted(A)) break;

		// swap two random items
		A.swap(rand() % A.size(), rand() % A.size());
	}
}

// ****************************************************************************
// *** Bitonic Sort

// from http://www.iti.fh-flensburg.de/lang/algorithmen/sortieren/bitonic/oddn.htm

namespace BitonicSortNS {

static const bool ASCENDING = true;    // sorting direction

static void compare(SortArray& A, int i, int j, bool dir)
{
	if (dir == (A[i] > A[j]))
		A.swap(i, j);
}

static void bitonicMerge(SortArray& A, int lo, int n, bool dir)
{
	if (n > 1)
	{
		int m = largestPowerOfTwoLessThan(n);

		for (int i = lo; i < lo + n - m; i++)
			compare(A, i, i+m, dir);

		bitonicMerge(A, lo, m, dir);
		bitonicMerge(A, lo + m, n - m, dir);
	}
}

static void bitonicSort(SortArray& A, int lo, int n, bool dir)
{
	if (n > 1)
	{
		int m = n / 2;
		bitonicSort(A, lo, m, !dir);
		bitonicSort(A, lo + m, n - m, dir);
		bitonicMerge(A, lo, n, dir);
	}
}

} // namespace BitonicSortNS

void BitonicSort(SortArray& A)
{
	BitonicSortNS::bitonicSort(A, 0, A.size(), BitonicSortNS::ASCENDING);
}

// ****************************************************************************
// *** Bitonic Sort as "Parallel" Sorting Network

// from http://www.iti.fh-flensburg.de/lang/algorithmen/sortieren/bitonic/oddn.htm

// modified to first record the recursively generated swap sequence, and then
// sort it back into the order a parallel sorting network would perform the
// swaps in

namespace BitonicSortNetworkNS {

	struct swappair_type
	{
	// swapped positions
		unsigned int i,j;

	// depth of recursions: sort / merge
		unsigned int sort_depth, merge_depth;

		swappair_type(unsigned int _i, unsigned int _j,
			unsigned int _sort_depth, unsigned int _merge_depth)
		: i(_i), j(_j),
		sort_depth(_sort_depth), merge_depth(_merge_depth)
		{ }

	// order relation for sorting swaps
		bool operator < (const swappair_type& b) const
		{
			if (sort_depth != b.sort_depth)
				return sort_depth > b.sort_depth;

			if (merge_depth != b.merge_depth)
				return merge_depth < b.merge_depth;

			return i < b.i;
		}
	};

	typedef std::vector<swappair_type> sequence_type;
	std::vector<swappair_type> sequence;

	void replay(SortArray& A)
	{
		for (sequence_type::const_iterator si = sequence.begin();
			si != sequence.end(); ++si)
		{
			if (A[si->i] > A[si->j])
				A.swap(si->i, si->j);
		}
	}

static const bool ASCENDING = true; // sorting direction

static void compare(SortArray& /* A */, unsigned int i, unsigned int j, bool dir,
unsigned int sort_depth, unsigned int merge_depth)
{
	// if (dir == (A[i] > A[j])) A.swap(i, j);

	if (dir)
		sequence.push_back( swappair_type(i,j, sort_depth, merge_depth) );
	else
		sequence.push_back( swappair_type(j,i, sort_depth, merge_depth) );
}

static void bitonicMerge(SortArray& A, unsigned int lo, unsigned int n, bool dir,
	unsigned int sort_depth, unsigned int merge_depth)
{
	if (n > 1)
	{
		unsigned int m = largestPowerOfTwoLessThan(n);

		for (unsigned int i = lo; i < lo + n - m; i++)
			compare(A, i, i + m, dir, sort_depth, merge_depth);

		bitonicMerge(A, lo, m, dir, sort_depth, merge_depth+1);
		bitonicMerge(A, lo + m, n - m, dir, sort_depth, merge_depth+1);
	}
}

static void bitonicSort(SortArray& A, unsigned int lo, unsigned int n, bool dir,
	unsigned int sort_depth)
{
	if (n > 1)
	{
		unsigned int m = n / 2;
		bitonicSort(A, lo, m, !dir, sort_depth+1);
		bitonicSort(A, lo + m, n - m, dir, sort_depth+1);
		bitonicMerge(A, lo, n, dir, sort_depth, 0);
	}
}

void sort(SortArray& A)
{
	sequence.clear();
	bitonicSort(A, 0, A.size(), BitonicSortNS::ASCENDING, 0);
	std::sort(sequence.begin(), sequence.end());
	replay(A);
	sequence.clear();
}

} // namespace BitonicSortNS

void BitonicSortNetwork(SortArray& A)
{
	BitonicSortNetworkNS::sort(A);
}

// ****************************************************************************
// *** Batcher's Odd-Even Merge Sort as "Parallel" Sorting Network

// from http://www.iti.fh-flensburg.de/lang/algorithmen/sortieren/networks/oemen.htm

// modified to first record the recursively generated swap sequence, and then
// sort it back into the order a parallel sorting network would perform the
// swaps in

namespace BatcherSortNetworkNS {

	struct swappair_type
	{
	// swapped positions
		unsigned int i,j;

	// depth of recursions: sort / merge
		unsigned int sort_depth, merge_depth;

		swappair_type(unsigned int _i, unsigned int _j,
			unsigned int _sort_depth, unsigned int _merge_depth)
		: i(_i), j(_j),
		sort_depth(_sort_depth), merge_depth(_merge_depth)
		{ }

	// order relation for sorting swaps
		bool operator < (const swappair_type& b) const
		{
			if (sort_depth != b.sort_depth)
				return sort_depth > b.sort_depth;

			if (merge_depth != b.merge_depth)
				return merge_depth > b.merge_depth;

			return i < b.i;
		}
	};

	typedef std::vector<swappair_type> sequence_type;
	std::vector<swappair_type> sequence;

	void replay(SortArray& A)
	{
		for (sequence_type::const_iterator si = sequence.begin();
			si != sequence.end(); ++si)
		{
			if (A[si->i] > A[si->j])
				A.swap(si->i, si->j);
		}
	}

	static void compare(SortArray& A, unsigned int i, unsigned int j,
		unsigned int sort_depth, unsigned int merge_depth)
	{
	// skip all swaps beyond end of array
		ASSERT(i < j);
		if (j >= A.size()) return;

		sequence.push_back( swappair_type(i,j, sort_depth, merge_depth) );

	//if (A[i] > A[j]) A.swap(i, j);
	}

// lo is the starting position and n is the length of the piece to be merged, r
// is the distance of the elements to be compared
	static void oddEvenMerge(SortArray& A, unsigned int lo, unsigned int n, unsigned int r,
		unsigned int sort_depth, unsigned int merge_depth)
	{
		unsigned int m = r * 2;
		if (m < n)
		{
		// even subsequence
			oddEvenMerge(A, lo, n, m, sort_depth, merge_depth+1);
		// odd subsequence
			oddEvenMerge(A, lo + r, n, m, sort_depth, merge_depth+1);

			for (unsigned int i = lo + r; i + r < lo + n; i += m)
				compare(A, i, i + r, sort_depth, merge_depth);
		}
		else {
			compare(A, lo, lo + r, sort_depth, merge_depth);
		}
	}

// sorts a piece of length n of the array starting at position lo
	static void oddEvenMergeSort(SortArray& A, unsigned int lo, unsigned int n,
		unsigned int sort_depth)
	{
		if (n > 1)
		{
			unsigned int m = n / 2;
			oddEvenMergeSort(A, lo, m, sort_depth+1);
			oddEvenMergeSort(A, lo + m, m, sort_depth+1);
			oddEvenMerge(A, lo, n, 1, sort_depth, 0);
		}
	}

	void sort(SortArray& A)
	{
		sequence.clear();

		unsigned int n = largestPowerOfTwoLessThan(A.size());
		if (n != A.size()) n *= 2;

		oddEvenMergeSort(A, 0, n, 0);
		std::sort(sequence.begin(), sequence.end());
		replay(A);
		sequence.clear();
	}

} // namespace BatcherSortNetworkNS

void BatcherSortNetwork(SortArray& A)
{
	BatcherSortNetworkNS::sort(A);
}

// ****************************************************************************
// *** Smooth Sort

// from http://en.wikipediA.org/wiki/Smoothsort

namespace SmoothSortNS {

	static const int LP[] = {
		1, 1, 3, 5, 9, 15, 25, 41, 67, 109,
		177, 287, 465, 753, 1219, 1973, 3193, 5167, 8361, 13529, 21891,
		35421, 57313, 92735, 150049, 242785, 392835, 635621, 1028457,
		1664079, 2692537, 4356617, 7049155, 11405773, 18454929, 29860703,
		48315633, 78176337, 126491971, 204668309, 331160281, 535828591,
	866988873 // the next number is > 31 bits.
};

static void sift(SortArray& A, int pshift, int head)
{
	// we do not use Floyd's improvements to the heapsort sift, because we
	// are not doing what heapsort does - always moving nodes from near
	// the bottom of the tree to the root.

	value_type val = A[head];

	while (pshift > 1)
	{
		int rt = head - 1;
		int lf = head - 1 - LP[pshift - 2];

		if (val.cmp(A[lf]) >= 0 && val.cmp(A[rt]) >= 0)
			break;

		if (A[lf].cmp(A[rt]) >= 0) {
			A.set(head, A[lf]);
			head = lf;
			pshift -= 1;
		}
		else {
			A.set(head, A[rt]);
			head = rt;
			pshift -= 2;
		}
	}

	A.set(head, val);
}

static void trinkle(SortArray& A, int p, int pshift, int head, bool isTrusty)
{
	value_type val = A[head];

	while (p != 1)
	{
		int stepson = head - LP[pshift];

		if (A[stepson].cmp(val) <= 0)
			break; // current node is greater than head. sift.

		// no need to check this if we know the current node is trusty,
		// because we just checked the head (which is val, in the first
		// iteration)
		if (!isTrusty && pshift > 1) {
			int rt = head - 1;
			int lf = head - 1 - LP[pshift - 2];
			if (A[rt].cmp(A[stepson]) >= 0 ||
				A[lf].cmp(A[stepson]) >= 0)
				break;
		}

		A.set(head, A[stepson]);

		head = stepson;
		//int trail = Integer.numberOfTrailingZeros(p & ~1);
		int trail = __builtin_ctz(p & ~1);
		p >>= trail;
		pshift += trail;
		isTrusty = false;
	}

	if (!isTrusty) {
		A.set(head, val);
		sift(A, pshift, head);
	}
}

void sort(SortArray& A, int lo, int hi)
{
	int head = lo; // the offset of the first element of the prefix into m

	// These variables need a little explaining. If our string of heaps
	// is of length 38, then the heaps will be of size 25+9+3+1, which are
	// Leonardo numbers 6, 4, 2, 1.
	// Turning this into a binary number, we get b01010110 = 0x56. We represent
	// this number as a pair of numbers by right-shifting all the zeros and
	// storing the mantissa and exponent as "p" and "pshift".
	// This is handy, because the exponent is the index into L[] giving the
	// size of the rightmost heap, and because we can instantly find out if
	// the rightmost two heaps are consecutive Leonardo numbers by checking
	// (p&3)==3

	int p = 1; // the bitmap of the current standard concatenation >> pshift
	int pshift = 1;

	while (head < hi)
	{
		if ((p & 3) == 3) {
			// Add 1 by merging the first two blocks into a larger one.
			// The next Leonardo number is one bigger.
			sift(A, pshift, head);
			p >>= 2;
			pshift += 2;
		}
		else {
			// adding a new block of length 1
			if (LP[pshift - 1] >= hi - head) {
				// this block is its final size.
				trinkle(A, p, pshift, head, false);
			} else {
				// this block will get merged. Just make it trusty.
				sift(A, pshift, head);
			}

			if (pshift == 1) {
				// LP[1] is being used, so we add use LP[0]
				p <<= 1;
				pshift--;
			} else {
				// shift out to position 1, add LP[1]
				p <<= (pshift - 1);
				pshift = 1;
			}
		}
		p |= 1;
		head++;
	}

	trinkle(A, p, pshift, head, false);

	while (pshift != 1 || p != 1)
	{
		if (pshift <= 1) {
			// block of length 1. No fiddling needed
			//int trail = Integer.numberOfTrailingZeros(p & ~1);
			int trail = __builtin_ctz(p & ~1);
			p >>= trail;
			pshift += trail;
		}
		else {
			p <<= 2;
			p ^= 7;
			pshift -= 2;

			// This block gets broken into three bits. The rightmost bit is a
			// block of length 1. The left hand part is split into two, a block
			// of length LP[pshift+1] and one of LP[pshift].  Both these two
			// are appropriately heapified, but the root nodes are not
			// necessarily in order. We therefore semitrinkle both of them

			trinkle(A, p >> 1, pshift + 1, head - LP[pshift] - 1, true);
			trinkle(A, p, pshift, head - 1, true);
		}

		head--;
	}
}

} // namespace SmoothSortNS

void SmoothSort(SortArray& A)
{
	return SmoothSortNS::sort(A, 0, A.size()-1);
}

// ****************************************************************************
// *** Stooge Sort

void StoogeSort(SortArray& A, int i, int j)
{
	if (A[i] > A[j])
	{
		A.swap(i, j);
	}

	if (j - i + 1 >= 3)
	{
		int t = (j - i + 1) / 3;

		A.mark(i, 3);
		A.mark(j, 3);

		StoogeSort(A, i, j-t);
		StoogeSort(A, i+t, j);
		StoogeSort(A, i, j-t);

		A.unmark(i);
		A.unmark(j);
	}
}

void StoogeSort(SortArray& A)
{
	StoogeSort(A, 0, A.size()-1);
}

// ****************************************************************************
// *** Slow Sort

void SlowSort(SortArray& A, int i, int j)
{
	if (i >= j) return;

	int m = (i + j) / 2;

	SlowSort(A, i, m);
	SlowSort(A, m+1, j);

	if (A[m] > A[j])
		A.swap(m, j);

	A.mark(j, 2);

	SlowSort(A, i, j-1);

	A.unmark(j);
}

void SlowSort(SortArray& A)
{
	SlowSort(A, 0, A.size()-1);
}

// ****************************************************************************
// *** Cycle Sort

// Adapted from http://en.wikipedia.org/wiki/Cycle_sort

void CycleSort(SortArray& array, ssize_t n)
{
	ssize_t cycleStart = 0;

	volatile ssize_t cycleMark = 0;
	array.watch(&cycleMark, 16);

	volatile ssize_t rank = 0;
	array.watch(&rank, 3);

	// Loop through the array to find cycles to rotate.
	for (cycleStart = 0; cycleStart < n - 1; ++cycleStart)
	{
		// first check if already in place
		if(array.get_mark(cycleStart) == 2)
			continue;

		const value_type& item = array[cycleStart];
		cycleMark = cycleStart;

		do {
			// Find where to put the item, taking stable-sort characteristics into account.
			rank = cycleStart;
			for (ssize_t i = cycleStart + 1; i < n; ++i)
			{
				if(array.get_mark(i) == 2)
					continue;

				if ((rank < cycleMark) ? (array[i] <= item) : (array[i] < item)) {
					do {
						rank++;
					} while(array.get_mark(rank) == 2);
				}
			}

			// If the item is already there, this is a 1-cycle.
			if (rank == cycleStart) {
				array.mark(rank, 2);
				break;
			}

			// Otherwise, put the item after any duplicates.
			//while (item == array[rank])
			//	rank++;

			// Put item into right place and colorize
			array.swap(rank, cycleStart);
			array.mark(rank, 2);

			// Continue for rest of the cycle.
			cycleMark = rank;
		}
		while (rank != cycleStart);
	}

	array.unwatch_all();
}

void CycleSort(SortArray& A)
{
	CycleSort(A, A.size());
}

// ****************************************************************************
// *** Splay Sort

// Inserts all elements into a splay tree, then traverses that tree to discover
// the sorted order.  This takes O(n log n) operations and O(n) extra space.
// This implementation uses the semi-splay tree variant, and moves the data
// in-place for better visuals.

namespace Splay {
	typedef struct {
		size_t idx, parent, left, right;
	} SplayNode;

	class SplayTree {
	public:
		SortArray& data;
		std::vector<SplayNode> tree;
		size_t root;

		SplayTree(SortArray& A, size_t n=0) : data(A), root(0) {
			tree.reserve(n);
		}

		// rotates a node with its parent
		void rotate(size_t i) {
			size_t j = tree[i].parent;

			if(i == j) return;  // root node
			if(tree[j].left == i) {
				// left-hand rotation
				if(tree[i].right != i) {
					tree[j].left = tree[i].right;
					tree[tree[j].left].parent = j;
				} else {
					// no child here
					tree[j].left = j;
				}
				tree[i].right = j;

				if(tree[j].parent == j) {
					// parent is root, make ourselves root instead
					tree[i].parent = root = i;
				} else {
					size_t k = tree[i].parent = tree[j].parent;
					if(tree[k].left == j)
						tree[k].left = i;
					else
						tree[k].right = i;
				}
				tree[j].parent = i;
			} else {
				// right-hand rotation
				if(tree[i].left != i) {
					tree[j].right = tree[i].left;
					tree[tree[j].right].parent = j;
				} else {
					// no child here
					tree[j].right = j;
				}
				tree[i].left = j;

				if(tree[j].parent == j) {
					// parent is root, make ourselves root instead
					tree[i].parent = root = i;
				} else {
					size_t k = tree[i].parent = tree[j].parent;
					if(tree[k].left == j)
						tree[k].left = i;
					else
						tree[k].right = i;
				}
				tree[j].parent = i;
			}
		}

		// splays a node towards the root
		void splay(size_t i) {
			size_t j = tree[i].parent;
			size_t k = tree[j].parent;

			if(i == j) return;  // root node
			if(j == k) {
				// zig splay; rotate root's child to root
				rotate(i);
			} else if((tree[j].left == i && tree[k].left == j) || (tree[j].right == i && tree[k].right == j)) {
				// zig-zig semi-splay; rotate parent with grandparent, then continue with parent
				rotate(j);
				splay(j);
			} else {
				// zig-zag splay; rotate child with parent *and* with new parent after that, then continue
				rotate(i);
				rotate(i);
				splay(i);
			}
		}

		// iterates through the tree in order, without splaying
		size_t first(void) const {
			size_t i = root;
			while(tree[i].left != i)
				i = tree[i].left;
			return i;
		}
		size_t last(void) const {
			size_t i = root;
			while(tree[i].right != i)
				i = tree[i].right;
			return i;
		}
		size_t next(size_t i) const {
			if(tree[i].right != i) {
				// return leftmost child of right-hand child
				for(i = tree[i].right; i != tree[i].left; i = tree[i].left)
					;
				return i;
			} else while(1) {
				// back out one level of tree, if possible
				size_t j = tree[i].parent;
				if(j == i)
					return first(); // root node, wrap around
				if(tree[j].left == i)
					return j;       // parent is the next node

				// we're a right child, keep backing out
				i = j;
			}
		}
		size_t prev(size_t i) const {
			if(tree[i].left != i) {
				// return rightmost child of left-hand child
				for(i = tree[i].left; i != tree[i].right; i = tree[i].right)
					;
				return i;
			} else while(1) {
				// back out one level of tree, if possible
				size_t j = tree[i].parent;
				if(j == i)
					return last();  // root node, wrap around
				if(tree[j].right == i)
					return j;       // parent is the next node

				// we're a left child, keep backing out
				i = j;
			}
		}

		// locates an item from data[] in the tree, without splaying
		// assumes item is actually present, returns root node otherwise
		size_t find(size_t i) const {
			for(size_t j=0; j < tree.size(); j++)
				if(tree[j].idx == i)
					return j;
			return root;
		}

		// inserts an item from data[] into the tree, then splays it
		void insert(size_t i, const bool goingLeft=false) {
			size_t j = root;
			size_t k = tree.size();
			bool direction = false;
			SplayNode n;

			n.idx = i;
			n.parent = n.left = n.right = k;

			if(!k) {
				// adding first node
				tree.push_back(n);
				return;
			}

			do {
				n.parent = j;
				if(goingLeft) {
					direction = (data[i] <= data[tree[j].idx]);
				} else {
					direction = (data[i] <  data[tree[j].idx]);
				}
				if(direction)
					j = tree[j].left;
				else
					j = tree[j].right;
			} while(j != n.parent);

			// we've found a leaf branch
			(direction ? tree[j].left : tree[j].right) = k;
			tree.push_back(n);

			// now rebalance the tree
			splay(k);
		}

		// removes a node from the tree; this invalidates indices into the tree
		void remove(size_t i) {
			if(tree[i].left != i && tree[i].right != i) {
				// node has two children, so swap it with its neighbour (which must be a leaf), and delete that item instead
				size_t j = next(i);
				std::swap(tree[i].idx, tree[j].idx);
				i = j;

				j = tree[i].parent;
				if(tree[j].left == i)
					tree[j].left = j;
				else
					tree[j].right = j;
			} else if(tree[i].left != i) {
				// item has only a left child, so reparent it
				size_t j = tree[i].parent;
				size_t k = tree[i].left;

				if(j == i) {
					// we're the root node
					tree[k].parent = k;
					root = k;
				} else {
					tree[k].parent = j;
					if(tree[j].left == i)
						tree[j].left = k;
					else
						tree[j].right = k;
				}
			} else if(tree[i].right != i) {
				// item has only a right child, so reparent it
				size_t j = tree[i].parent;
				size_t k = tree[i].right;

				if(j == i) {
					// we're the root node
					tree[k].parent = k;
					root = k;
				} else {
					tree[k].parent = j;
					if(tree[j].left == i)
						tree[j].left = k;
					else
						tree[j].right = k;
				}
			} else {
				// item is a leaf; detach it from the tree
				size_t j = tree[i].parent;
				if(j == i) {
					// we're the root node, and also a leaf - nothing to do
				} else {
					// we were a leaf, now our parent forgets about us
					if(tree[j].left == i)
						tree[j].left = j;
					else
						tree[j].right = j;
				}
			}

			// node i is now an orphan; swap it to the end of the array for deletion
			size_t j = tree.size() - 1;
			if(i != j) {
				tree[i].idx = tree[j].idx;
				if(tree[j].left == j) {
					tree[i].left = i;
				} else {
					size_t k = tree[i].left = tree[j].left;
					tree[k].parent = i;
				}
				if(tree[j].right == j) {
					tree[i].right = i;
				} else {
					size_t k = tree[i].right = tree[j].right;
					tree[k].parent = i;
				}
				if(tree[j].parent == j) {
					tree[i].parent = i;
					root = i;
				} else {
					size_t k = tree[i].parent = tree[j].parent;
					if(tree[k].left == j)
						tree[k].left = i;
					else
						tree[k].right = i;
				}
			}

			tree.pop_back();
		}
	};

	// a conventional splaysort
	// insert all array elements into the tree, then traverse it in order
	void sort(SortArray& A, size_t l, size_t r) {
		SplayTree tree(A, r-l);
		std::vector<size_t> rev;

		// Build the splay tree
		rev.reserve(r-l);
		for(size_t i=l; i < r; i++) {
			tree.insert(i);
			rev.push_back(i-l);
		}

		// Iterate over the items in sorted order
		for(size_t i=tree.first(), j=l; j < r; j++, i = tree.next(i)) {
			size_t k = tree.tree[i].idx;

			// we want to swap the item into the correct position
			// but we also need to update the tree node of the item currently here
			// so that it points to the correct place after the swap
			// rev[] contains references from item position to tree position
			if(k != j) {
				size_t x = rev[j-l];  // j;

				if(tree.tree[x].idx != j) {
					// this shouldn't happen
					x = tree.find(j);
					tree.splay(x);
				}

				A.swap(j,k);
				A.mark_swap(j,k);

				tree.tree[x].idx = k;
				tree.tree[i].idx = j;

				rev[j-l] = i;
				rev[k-l] = x;
			}
		}
	}

	// a splay-tree accelerated version of cocktail-shaker sort
	// a search window of width m+1 (m defaults to sqrt(r-l)) is rolled back and forth
	// so up to m items can be carried along in a single pass, instad of just one
	// with m == r-l, this reduces to a plain splaysort
	// with m == 1, this reduces to a plain cocktail shaker sort
	void shake(SortArray& A, size_t l, size_t r, size_t m = 32) {
		if(!m) {
			while(m*m <= r-l)
				m++;
			m--;
		}
		SplayTree tree(A, m+1);
		size_t i=l, j=l, z=l;

		// begin by inserting first m elements into tree
		while(j < r && j-i < m) {
			tree.insert(j++);
		}

		while(r > l) {
			// ascending pass
			z = l;
			while(j < r) {
				// extend window to right
				tree.insert(j++, false);

				// move smallest item in window to the left edge
				size_t x = tree.first();
				size_t k = tree.tree[x].idx;

				if(k == j-1)
					z = i+1;  // item moving directly from right edge to left edge

				if(k != i) {
					size_t y = tree.find(i);

					A.swap(i,k);
					A.mark_swap(i,k);

					tree.tree[x].idx = i;
					tree.tree[y].idx = k;
				}

				// shrink window on the left
				tree.remove(x);
				i++;
			}

			// reduce iteration width on the right
			r = z;
			if(r <= l)
				break;

			// descending pass
			z = r;
			while(i-- > l) {
				// extend window to left
				tree.insert(i, true);

				// move largest item in window to the right edge
				j--;
				size_t x = tree.last();
				size_t k = tree.tree[x].idx;

				if(k == i)
					z = j;  // item moving directly from left edge to right edge

				if(k != j) {
					size_t y = tree.find(j);

					A.swap(j,k);
					A.mark_swap(j,k);

					tree.tree[x].idx = j;
					tree.tree[y].idx = k;
				}

				// shrink window on the right
				tree.remove(x);
			}
			i++;

			// reduce iteration width on the left
			l = z;
		}

		// ensure items in final window are correctly positioned
		while(i < j) {
			// move smallest item in window to the left edge
			size_t x = tree.first();
			size_t k = tree.tree[x].idx;
			if(k != i) {
				size_t y = tree.find(i);

				A.swap(i,k);
				A.mark_swap(i,k);

				tree.tree[x].idx = i;
				tree.tree[y].idx = k;
			}

			// shrink window on the left
			tree.remove(x);
			i++;
		}
	}

	// Collect a series of runs, as long as possible within the window size given.
	std::vector<size_t> runs(SortArray& A, size_t m = 32) {
		std::vector<size_t> out;
		SplayTree tree(A, m+1);
		size_t i,j,k;

		for(i=0, j=0, k=0; i < A.size(); i++) {
			// extend window to right
			tree.insert(i);

			// check whether we need to flush this run and start a new one
			if(j > k && tree.find(i) == tree.first() && A[i] < A[j-1]) {
				// flush
				tree.remove(tree.first());

				while(j < i) {
					size_t x = tree.first();
					size_t w = tree.tree[x].idx;
					if(w != j) {
						size_t y = tree.find(j);

						A.swap(j,w);
						A.mark_swap(j,w);

						tree.tree[x].idx = j;
						tree.tree[y].idx = w;
					}
					tree.remove(x);
					j++;
				}

				// start new run
				out.push_back(k);
				k = j;
				tree.insert(i);
			}

			// push any overflowing value out on the left
			if(i-j > m) {
				size_t x = tree.first();
				size_t w = tree.tree[x].idx;
				if(w != j) {
					size_t y = tree.find(j);

					A.swap(j,w);
					A.mark_swap(j,w);

					tree.tree[x].idx = j;
					tree.tree[y].idx = w;
				}
				tree.remove(x);
				j++;
			}
		}

		// flush final run
		while(j < i) {
			size_t x = tree.first();
			size_t w = tree.tree[x].idx;
			if(w != j) {
				size_t y = tree.find(j);

				A.swap(j,w);
				A.mark_swap(j,w);

				tree.tree[x].idx = j;
				tree.tree[y].idx = w;
			}
			tree.remove(x);
			j++;
		}

		out.push_back(k);
		out.push_back(A.size());

		return out;
	}
};

void SplaySort(SortArray& A)
{
	Splay::sort(A, 0, A.size());
}

void SplaySort(SortArray& A, size_t l, size_t r)
{
	Splay::sort(A, l, r);
}

void SplayShakeSort(SortArray& A)
{
	Splay::shake(A, 0, A.size());
}

void SplayShakeSort(SortArray& A, size_t m)
{
	Splay::shake(A, 0, A.size(), m);
}

void SplayMergeSort(SortArray& A)
{	std::vector<size_t> runs = Splay::runs(A);

	while(runs.size() > 2)
		CataMergeRuns(A, runs, SMALL_MERGE);
}

// ****************************************************************************

