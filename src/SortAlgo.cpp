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
#include "algorithms/quicksort.h"
#include "algorithms/merge.h"
#include "algorithms/heap.h"
#include "algorithms/parallel.h"

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

