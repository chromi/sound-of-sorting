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

#include <algorithm>
#include <numeric>
#include <limits>
#include <inttypes.h>

typedef ArrayItem value_type;

// inversion count limit for iterator instrumented algorithms
const unsigned int inversion_count_instrumented = 512;

const struct AlgoEntry g_algolist[] =
{
    { _("Selection Sort"), &SelectionSort, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Insertion Sort"), &InsertionSort, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Binary Insertion Sort"), &BinaryInsertionSort, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Merge Sort"), &MergeSort, UINT_MAX, 512,
      _("Merge sort which merges two sorted sequences into a shadow array,"
        "and then copies it back to the shown array.") },
    { _("Merge Sort (iterative)"), &MergeSortIterative, UINT_MAX, 512,
      _("Merge sort variant which iteratively merges "
        "subarrays of sizes of powers of two.") },
    { _("Merge Sort (in-place)"), &MergeSortInPlace, UINT_MAX, 512,
      _("Merge sort variant which iteratively merges "
        "subarrays of sizes of powers of two, using an in-place merging algorithm.") },
    { _("Merge Sort (semi-in-place)"), &MergeSortSemiInPlace, UINT_MAX, 512,
      _("Merge sort variant which iteratively merges "
        "subarrays of sizes of powers of two, using a fixed amount of temporary storage.") },
    { _("CataMerge Sort"), &CataMergeSort, UINT_MAX, 512,
      _("Merge sort variant which searches for runs in either direction, reverses descending runs, then merges them.") },
    { _("Quick Sort (LR ptrs)"), &QuickSortLR, UINT_MAX, UINT_MAX,
      _("Quick sort variant with left and right pointers.") },
    { _("Quick Sort (LL ptrs)"), &QuickSortLL, UINT_MAX, UINT_MAX,
      _("Quick sort variant from 3rd edition of CLRS: two pointers on left.") },
    { _("Quick Sort (ternary, LR ptrs)"), &QuickSortTernaryLR, UINT_MAX, UINT_MAX,
      _("Ternary-split quick sort variant, adapted from multikey quicksort by "
        "Bentley & Sedgewick: partitions \"=<?>=\" using two pairs of pointers "
        "at left and right, then copied to middle.") },
    { _("Quick Sort (ternary, LL ptrs)"), &QuickSortTernaryLL, UINT_MAX, UINT_MAX,
      _("Ternary-split quick sort variant: partitions \"<>?=\" using two "
        "pointers at left and one at right. Afterwards copies the \"=\" to middle.") },
    { _("Quick Sort (dual pivot)"), &QuickSortDualPivot, UINT_MAX, UINT_MAX,
      _("Dual pivot quick sort variant: partitions \"<1<2?>\" using three pointers, "
        "two at left and one at right.") },
    { _("Competent QuickSort"), &QuickSortCompetent, UINT_MAX, UINT_MAX,
      _("Ternary-split quicksort variant with the usual practical implementation features: "
        "median-of-three pivot, insertion-sort of small blocks, pivot values' position "
        "established without a separate rearrangement pass, and smallest-first recursion "
        "to exploit tail-call optimisation.") },
    { _("Bubble Sort"), &BubbleSort, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Cocktail Shaker Sort"), &CocktailShakerSort, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Gnome Sort"), &GnomeSort, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Comb Sort"), &CombSort, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Shell Sort"), &ShellSort, UINT_MAX, 1024,
      wxEmptyString },
    { _("Heap Sort"), &HeapSort, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Smooth Sort"), &SmoothSort, UINT_MAX, 1024,
      wxEmptyString },
    { _("Odd-Even Sort"), &OddEvenSort, UINT_MAX, 1024,
      wxEmptyString },
    // older sequential implementation, which really makes little sense to do
    //{ _("Bitonic Sort"), &BitonicSort, UINT_MAX, UINT_MAX, wxEmptyString },
    { _("Batcher's Bitonic Sort"), &BitonicSortNetwork, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Batcher's Odd-Even Merge Sort"), &BatcherSortNetwork, UINT_MAX, UINT_MAX,
      wxEmptyString },
    { _("Cycle Sort"), &CycleSort, 512, UINT_MAX,
      wxEmptyString },
    { _("Radix Sort (LSD)"), &RadixSortLSD, UINT_MAX, 512,
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
    { _("Bogo Sort"), &BogoSort, 10, UINT_MAX,
      wxEmptyString },
    { _("Bozo Sort"), &BozoSort, 10, UINT_MAX,
      wxEmptyString },
    { _("Stooge Sort"), &StoogeSort, 256, inversion_count_instrumented,
      wxEmptyString },
    { _("Slow Sort"), &SlowSort, 128, inversion_count_instrumented,
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

// ****************************************************************************
// *** Insertion Sort

// swaps every time (keeps all values visible)
void InsertionSort(SortArray& A)
{
    for (size_t i = 1; i < A.size(); ++i)
    {
        value_type key = A[i];
        A.mark(i);

        ssize_t j = i - 1;
        while (j >= 0 && A[j] > key)
        {
            A.swap(j, j+1);
            j--;
        }

        A.unmark(i);
    }
}

// with extra item on stack
void InsertionSort2(SortArray& A)
{
    for (size_t i = 1; i < A.size(); ++i)
    {
        value_type tmp, key = A[i];
        A.mark(i);

        ssize_t j = i - 1;
        while (j >= 0 && (tmp = A[j]) > key)
        {
            A.set(j + 1, tmp);
            j--;
        }
        A.set(j + 1, key);

        A.unmark(i);
    }
}

// swaps every time (keeps all values visible)
void BinaryInsertionSort(SortArray& A)
{
    for (size_t i = 1; i < A.size(); ++i)
    {
        value_type key = A[i];
        A.mark(i);

        size_t lo = 0, hi = i;
        while (lo < hi) {
            size_t mid = (lo + hi) / 2;
            if (key < A[mid])
                hi = mid;
            else
                lo = mid + 1;
        }

        // item has to go into position lo

        size_t j = i;
        while (j > lo)
        {
            A.set(j, A[j-1]);
            j--;
        }
        if(lo < i)
            A.set(lo, key);

        A.unmark(i);
    }
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

#define MERGESORT_INPLACE_THRESHOLD (16)

void MergeSortSwapBlocks(SortArray& A, const size_t l, const size_t m, const size_t r)
{
    // We have two sorted, adjacent blocks (not necessarily of equal size) of which the last element of the right block sorts before
    // the first element of the left block.  Our task is therefore to exchange them as efficiently as is practical, keeping order.
    const size_t a = r-m, b = m-l;

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

    ASSERT(m-l <= MERGESORT_INPLACE_THRESHOLD);

    // Deal with trivial and simple cases first:

    // Either of the blocks is zero-length?
    if(m <= l || r <= l)
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
        MergeSortSwapBlocks(A, l, m, r);
        return;
    }

    // Okay, down to business.
    value_type tmp[MERGESORT_INPLACE_THRESHOLD];
    size_t i=l, j=m, x=0, y=0;

    while(i < j) {
        if(x >= y || (j < r && tmp[x] > A[j])) {
            // use right item
            while(i < m && A[i] <= A[j])
                i++;
            if(i >= j)
                break;

            if(i >= m) {
                // fill hole left by used right elements
                A.mark_swap(i,j);
                A.swap(i++, j++);
            } else if(j+1 < r && A[i] <= A[j+1]) {
                // store left element at head of remaining right block, preserving order
                A.mark_swap(i,j);
                A.swap(i++, j);
            } else {
                // store left element in tmp array
                A.mark_swap(i,j);
                A.mark(j, 12);
                tmp[y++] = A[i];
                A.set(i++, A[j++]);
            }
        } else {
            // use item from tmp array, which always sorts before remaining left items
            A.mark(i, 4);
            if(i < m)
                tmp[y++] = A[i];
            A.set(i++, tmp[x++]);
        }
    }
}

void MergeSortMergeInPlace(SortArray& A, const size_t l, const size_t m, const size_t r, const bool smallOpt, const bool root=false)
{
    // We have two sorted blocks in [l..m) and [m..r), which we must merge into a single sorted block in [l..r).
    // First, deal with trivial cases:

    // Either of the blocks is zero-length?
    if(m <= l || r <= l)
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
        MergeSortSwapBlocks(A, l, m, r);
        return;
    }

    // Proceed by swapping the end of the left block with the beginning of the right block, preserving order,
    // with the length of the swapped blocks chosen so that after the swap, all elements on the left sort before
    // all elements on the right.
    // We use a binary search to efficiently determine this length, comparing mirrored pairs of elements.

    size_t x=l, y=m, z=l, zz=(m*2-1) - z;

    if(zz > r-1) {
        // The right block is smaller than the left block.
        zz = r-1;
        x = z = m*2-r;
    }

    while(x < y) {
        if(A[z] <= A[zz])
            x = z+1;
        else
            y = z;
        z  = (x+y)/2;
        zz = (m*2-1) - z;
    }

    for(size_t i=z, j=m; i < m; i++, j++) {
        A.swap(i,j);
        A.mark_swap(i,j);
    }
    zz++;

    // This yields four smaller sorted blocks (of which up to two may be zero length).
    // Recursively merge the two pairs of blocks.
    // This recursion is what makes this algorithm O(N * (log N)^2) instead of O(N log N).
    if(z > l) {
        if(smallOpt && z-l <= MERGESORT_INPLACE_THRESHOLD)
            MergeSortMergeSmall(A, l, z, m);
        else
            MergeSortMergeInPlace(A, l, z, m, smallOpt);
    }
    if(zz < r) {
        if(smallOpt && zz-m <= MERGESORT_INPLACE_THRESHOLD)
            MergeSortMergeSmall(A, m, zz, r);
        else
            MergeSortMergeInPlace(A, m, zz, r, smallOpt);
    }
}

void MergeSortInPlace(SortArray& A, const size_t l, const size_t r, const bool smallOpt)
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

            if(smallOpt && s <= MERGESORT_INPLACE_THRESHOLD)
                MergeSortMergeSmall(A, i, j, k, true);
            else
                MergeSortMergeInPlace(A, i, j, k, smallOpt, true);
        }
    }
}

// This version is truly in-place, using no temporary arrays.
void MergeSortInPlace(SortArray& A)
{
    MergeSortInPlace(A, 0, A.size(), false);
}

// This version switches to a conventional mergesort for small merges, using O(1) extra memory.
void MergeSortSemiInPlace(SortArray& A)
{
    MergeSortInPlace(A, 0, A.size(), true);
}

// ****************************************************************************
// *** CataMerge Sort
//
// An adaptive, non-stable, in-place mergesort variant.  The array is examined for increasing
// and decreasing runs of values.  Decreasing runs are reversed to make them increasing runs.
// A list of runs is kept; whenever the last run is bigger than the previous one (or the end
// of the array is reached), it is merged in-place with the previous run.
//
// Inspired by the abandoned "Catasort" algorithm:  https://www.youtube.com/watch?v=ND6sC_ZzUHM
// According to the author, this name is a contraction of "Catapillar sort".
//
// As far as I can tell, Catasort repeatedly identifies decreasing runs and reverses
// them, making it a sort of generalised pancake sort.  In practice the performance and
// behaviour are similar to bubble or cocktail sort, except when the whole array is in
// descending order.  By combining this idea with mergesort, considerably better behaviour
// should result in the general case.

void CataMergeRuns(SortArray& A, std::vector<size_t>& runs)
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

	if(k-l > MERGESORT_INPLACE_THRESHOLD)
		MergeSortMergeInPlace(A, l, k, j, true, true);
	else
		MergeSortMergeSmall(A, l, k, j, true);

	runs.erase(runs.begin() + mini+1);
}

void CataMergeSort(SortArray& A)
{
	std::vector<size_t> runs;
	size_t i=0, j=0;
	int runPolarity = 0;

	runs.push_back(0);

	while(++j < A.size()) {
		int c = (A[j] < A[j-1]) ? -1 : 1;

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
				size_t kk = j-k, ll = k-l;

				// is the last run at least as big as the previous one?
				if(kk < ll)
					break;

				// both true, so merge required; repeat as necessary
				CataMergeRuns(A, runs);
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
		CataMergeRuns(A, runs);
}

// ****************************************************************************
// *** Quick Sort Pivot Selection

QuickSortPivotType g_quicksort_pivot = PIVOT_FIRST;

// some quicksort variants use hi inclusive and some exclusive, we require it
// to be _exclusive_. hi == array.end()!
ssize_t QuickSortSelectPivot(SortArray& A, ssize_t lo, ssize_t hi)
{
    if (g_quicksort_pivot == PIVOT_FIRST)
        return lo;

    if (g_quicksort_pivot == PIVOT_LAST)
        return hi-1;

    if (g_quicksort_pivot == PIVOT_MID)
        return (lo + hi) / 2;

    if (g_quicksort_pivot == PIVOT_RANDOM)
        return lo + (rand() % (hi - lo));

    if (g_quicksort_pivot == PIVOT_MEDIAN3)
    {
        ssize_t mid = (lo + hi) / 2;

        // cases if two are equal
        if (A[lo] == A[mid]) return lo;
        if (A[lo] == A[hi-1] || A[mid] == A[hi-1]) return hi-1;

        // cases if three are different
        return A[lo] < A[mid]
            ? (A[mid] < A[hi-1] ? mid : (A[lo] < A[hi-1] ? hi-1 : lo))
            : (A[mid] > A[hi-1] ? mid : (A[lo] < A[hi-1] ? lo : hi-1));
    }

    return lo;
}

wxArrayString QuickSortPivotText()
{
    wxArrayString sl;

    sl.Add( _("First Item") );
    sl.Add( _("Last Item") );
    sl.Add( _("Middle Item") );
    sl.Add( _("Random Item") );
    sl.Add( _("Median of Three") );

    return sl;
}

// ****************************************************************************
// *** Quick Sort LR (in-place, pointers at left and right, pivot is middle element)

// by myself (Timo Bingmann), based on Hoare's original code

void QuickSortLR(SortArray& A, ssize_t lo, ssize_t hi)
{
    // pick pivot and watch
    volatile ssize_t p = QuickSortSelectPivot(A, lo, hi+1);

    value_type pivot = A[p];
    A.watch(&p, 2);

    volatile ssize_t i = lo, j = hi;
    A.watch(&i, 3);
    A.watch(&j, 3);

    while (i <= j)
    {
        while (A[i] < pivot)
            i++;

        while (A[j] > pivot)
            j--;

        if (i <= j)
        {
            A.swap(i,j);

            // follow pivot if it is swapped
            if (p == i) p = j;
            else if (p == j) p = i;

            i++, j--;
        }
    }

    A.unwatch_all();

    if (lo < j)
        QuickSortLR(A, lo, j);

    if (i < hi)
        QuickSortLR(A, i, hi);
}

void QuickSortLR(SortArray& A)
{
    return QuickSortLR(A, 0, A.size()-1);
}

// ****************************************************************************
// *** Quick Sort LL (in-place, two pointers at left, pivot is first element and moved to right)

// by myself (Timo Bingmann), based on CLRS' 3rd edition

size_t PartitionLL(SortArray& A, size_t lo, size_t hi)
{
    // pick pivot and move to back
    size_t p = QuickSortSelectPivot(A, lo, hi);

    value_type pivot = A[p];
    A.swap(p, hi-1);
    A.mark(hi-1);

    volatile ssize_t i = lo;
    A.watch(&i, 3);

    for (size_t j = lo; j < hi-1; ++j)
    {
        if (A[j] <= pivot) {
            A.swap(i, j);
            ++i;
        }
    }

    A.swap(i, hi-1);
    A.unmark(hi-1);
    A.unwatch_all();

    return i;
}

void QuickSortLL(SortArray& A, size_t lo, size_t hi)
{
    if (lo + 1 < hi)
    {
        size_t mid = PartitionLL(A, lo, hi);

        QuickSortLL(A, lo, mid);
        QuickSortLL(A, mid+1, hi);
    }
}

void QuickSortLL(SortArray& A)
{
    return QuickSortLL(A, 0, A.size());
}

// ****************************************************************************
// *** Quick Sort Ternary (in-place, two pointers at left, pivot is first element and moved to right)

// by myself (Timo Bingmann), loosely based on multikey quicksort by B&S

void QuickSortTernaryLR(SortArray& A, ssize_t lo, ssize_t hi)
{
    if (hi <= lo) return;

    int cmp;

    // pick pivot and swap to back
    ssize_t piv = QuickSortSelectPivot(A, lo, hi+1);
    A.swap(piv, hi);
    A.mark(hi);

    const value_type& pivot = A[hi];

    // schema: |p ===  |i <<< | ??? |j >>> |q === |piv
    volatile ssize_t i = lo, j = hi-1;
    volatile ssize_t p = lo, q = hi-1;

    A.watch(&i, 3);
    A.watch(&j, 3);

    for (;;)
    {
        // partition on left
        while (i <= j && (cmp = A[i].cmp(pivot)) <= 0)
        {
            if (cmp == 0) {
                A.mark(p,4);
                A.swap(i, p++);
            }
            ++i;
        }

        // partition on right
        while (i <= j && (cmp = A[j].cmp(pivot)) >= 0)
        {
            if (cmp == 0) {
                A.mark(q,4);
                A.swap(j, q--);
            }
            --j;
        }

        if (i > j) break;

        // swap item between < > regions
        A.swap(i++, j--);
    }

    // swap pivot to right place
    A.swap(i,hi);
    A.mark_swap(i,hi);

    ssize_t num_less = i - p;
    ssize_t num_greater = q - j;

    // swap equal ranges into center, but avoid swapping equal elements
    j = i-1; i = i+1;

    ssize_t pe = lo + std::min(p-lo, num_less);
    for (ssize_t k = lo; k < pe; k++, j--) {
        A.swap(k,j);
        A.mark_swap(k,j);
    }

    ssize_t qe = hi-1 - std::min(hi-1-q, num_greater-1); // one already greater at end
    for (ssize_t k = hi-1; k > qe; k--, i++) {
        A.swap(i,k);
        A.mark_swap(i,k);
    }

    A.unwatch_all();
    A.unmark_all();

    QuickSortTernaryLR(A, lo, lo + num_less - 1);
    QuickSortTernaryLR(A, hi - num_greater + 1, hi);
}

void QuickSortTernaryLR(SortArray& A)
{
    return QuickSortTernaryLR(A, 0, A.size()-1);
}

// ****************************************************************************
// *** Quick Sort LL (in-place, two pointers at left, pivot is first element and moved to right)

// by myself (Timo Bingmann)

std::pair<ssize_t,ssize_t> PartitionTernaryLL(SortArray& A, ssize_t lo, ssize_t hi)
{
    // pick pivot and swap to back
    ssize_t p = QuickSortSelectPivot(A, lo, hi);

    value_type pivot = A[p];
    A.swap(p, hi-1);
    A.mark(hi-1);

    volatile ssize_t i = lo, k = hi-1;
    A.watch(&i, 3);

    for (ssize_t j = lo; j < k; ++j)
    {
        int cmp = A[j].cmp(pivot); // ternary comparison
        if (cmp == 0) {
            A.swap(--k, j);
            --j; // reclassify A[j]
            A.mark(k,4);
        }
        else if (cmp < 0) {
            A.swap(i++, j);
        }
    }

    // unwatch i, because the pivot is swapped there
    // in the first step of the following swap loop.
    A.unwatch_all();

    ssize_t j = i + (hi-k);

    for (ssize_t s = 0; s < hi-k; ++s) {
        A.swap(i+s, hi-1-s);
        A.mark_swap(i+s, hi-1-s);
    }
    A.unmark_all();

    return std::make_pair(i,j);
}

void QuickSortTernaryLL(SortArray& A, size_t lo, size_t hi)
{
    if (lo + 1 < hi)
    {
        std::pair<ssize_t,ssize_t> mid = PartitionTernaryLL(A, lo, hi);

        QuickSortTernaryLL(A, lo, mid.first);
        QuickSortTernaryLL(A, mid.second, hi);
    }
}

void QuickSortTernaryLL(SortArray& A)
{
    return QuickSortTernaryLL(A, 0, A.size());
}

// ****************************************************************************
// *** Dual-Pivot Quick Sort

// by Sebastian Wild

void dualPivotYaroslavskiy(class SortArray& a, int left, int right)
{
    if (right > left)
    {
        if (a[left] > a[right]) {
            a.swap(left, right);
        }

        const value_type p = a[left];
        const value_type q = a[right];

        a.mark(left);
        a.mark(right);

        volatile ssize_t l = left + 1;
        volatile ssize_t g = right - 1;
        volatile ssize_t k = l;

        a.watch(&l, 3);
        a.watch(&g, 3);
        a.watch(&k, 3);

        while (k <= g)
        {
            if (a[k] < p) {
                a.swap(k, l);
                ++l;
            }
            else if (a[k] >= q) {
                while (a[g] > q && k < g)  --g;
                a.swap(k, g);
                --g;

                if (a[k] < p) {
                    a.swap(k, l);
                    ++l;
                }
            }
            ++k;
        }
        --l;
        ++g;
        a.swap(left, l);
        a.swap(right, g);

        a.unmark_all();
        a.unwatch_all();

        dualPivotYaroslavskiy(a, left, l - 1);
        dualPivotYaroslavskiy(a, l + 1, g - 1);
        dualPivotYaroslavskiy(a, g + 1, right);
    }
}

void QuickSortDualPivot(class SortArray& a)
{
    return dualPivotYaroslavskiy(a, 0, a.size()-1);
}

// ****************************************************************************
// *** Competent QuickSort

// by Jonathan Morton

void QuickSortCompetent(class SortArray& A, ssize_t l, ssize_t r)
{
    if(r <= l+8) {
        // Small subarrays get insertion sorted.
        for(ssize_t i = l+1; i < r; i++) {
            const value_type t = A[i];
            ssize_t j;

            for(j = i; j > l; j--) {
                const value_type u = A[j-1];
                if(u <= t)
                    break;
                A.set(j, u);
            }
            if(j < i)
                A.set(j, t);
        }

        // Mark as completely sorted.
        for(ssize_t i = l; i < r; i++)
            A.mark(i, 2);
        return;
    }

    // Unconditionally use median-of-three pivot.
    // This can theoretically be subverted by crafted data, but this environment doesn't produce such data.
    value_type pivot;
    {
        ssize_t ll = l, rr = r-1;
        ssize_t mm = (l+r)/2;
        value_type Al = A[ll], Am = A[mm], Ar = A[rr];

        if(Al > Ar) {
            std::swap(Al,Ar);
            std::swap(ll,rr);
        }

        if(Al > Am) {
            std::swap(Al,Am);
            std::swap(ll,mm);
        }

        if(Am > Ar) {
            std::swap(Am,Ar);
            std::swap(mm,rr);
        }

        pivot = Am;

        // We don't unconditionally move the pivot value anywhere.
        // If it's out of position, it'll be corrected by the partitioning pass.
        // That will also mark the value as "equal to the pivot".
        // So we just mark it (and the block boundaries) once and forget about where we found it.
        A.mark(l,   3);
        A.mark(r-1, 3);
        A.mark(mm,  6);
    }

    // Ternary partitioning pass, leaving small values at left, large values at right, and pivot values in middle.
    // Shamelessly ripped from Yaroslavskiy dual-pivot, above, and adapted to suit.
    volatile ssize_t i=l, j=l, k=r-1;
    A.watch(&i, 4);
    A.watch(&j, 4);
    A.watch(&k, 4);

    while(j <= k) {
        const value_type v = A[j];
        const int cv = v.cmp(pivot);

        if(cv < 0) {
            if(i < j)
                A.swap(i, j);
            A.mark(j++, 6);
            A.mark(i++, 3);
        } else if(cv > 0) {
            value_type w;
            int cw;
            do {
                w = A[k];
                cw = w.cmp(pivot);
                if(cw > 0)
                    A.mark(k--, 3);
            } while(cw > 0);

            if(j > k)
                break;
            if(j < k)
                A.swap(j, k);
            A.mark(k--, 3);

            if(cw < 0) {
                A.swap(i, j);
                A.mark(j++, 6);
                A.mark(i++, 3);
            } else {
                A.mark(j++, 6);
            }
        } else {
            A.mark(j++, 6);
        }
    }

    A.unwatch_all();
    k++;

    // Mark pivot values as completely sorted, unmark all others.
    for(j=l; j < i; j++)
        A.unmark(j);
    for(j=i; j < k; j++)
        A.mark(j, 2);
    for(j=k; j < r; j++)
        A.unmark(j);

    // Sort the smaller partition first, so that the larger one can tail-recurse.
    // This guarantees O(log n) stack space requirement, assuming compiler is competent.
    // Don't use -O0; use -Og, -Os, -O1 or better.
    if(i-l < r-k) {
        QuickSortCompetent(A, l, i);
        QuickSortCompetent(A, k, r);
        return;
    } else {
        QuickSortCompetent(A, k, r);
        QuickSortCompetent(A, l, i);
        return;
    }
}

void QuickSortCompetent(class SortArray& A)
{
    QuickSortCompetent(A, 0, A.size());
}

// ****************************************************************************
// *** Bubble Sort

void BubbleSort(SortArray& A)
{
    for (size_t i = 0; i < A.size()-1; ++i)
    {
        for (size_t j = 0; j < A.size()-1 - i; ++j)
        {
            if (A[j] > A[j + 1])
            {
                A.swap(j, j+1);
            }
        }
    }
}

// ****************************************************************************
// *** Cocktail Shaker Sort

// from http://de.wikibooks.org/wiki/Algorithmen_und_Datenstrukturen_in_C/_Shakersort

void CocktailShakerSort(SortArray& A)
{
    size_t lo = 0, hi = A.size()-1, mov = lo;

    while (lo < hi)
    {
        for (size_t i = hi; i > lo; --i)
        {
            if (A[i-1] > A[i])
            {
                A.swap(i-1, i);
                mov = i;
            }
        }

        lo = mov;

        for (size_t i = lo; i < hi; ++i)
        {
            if (A[i] > A[i+1])
            {
                A.swap(i, i+1);
                mov = i;
            }
        }

        hi = mov;
    }
}

// ****************************************************************************
// *** Gnome Sort

// from http://en.wikipediA.org/wiki/Gnome_sort

void GnomeSort(SortArray& A)
{
    for (size_t i = 1; i < A.size(); )
    {
        if (A[i] >= A[i-1])
        {
            ++i;
        }
        else
        {
            A.swap(i, i-1);
            if (i > 1) --i;
        }
    }
}

// ****************************************************************************
// *** Comb Sort

// from http://en.wikipediA.org/wiki/Comb_sort

void CombSort(SortArray& A)
{
    const double shrink = 1.3;

    bool swapped = false;
    size_t gap = A.size();

    while ((gap > 1) || swapped)
    {
        if (gap > 1) {
            gap = (size_t)((float)gap / shrink);
        }

        swapped = false;

        for (size_t i = 0; gap + i < A.size(); ++i)
        {
            if (A[i] > A[i + gap])
            {
                A.swap(i, i+gap);
                swapped = true;
            }
        }
    }
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
// *** Shell Sort

// with gaps by Robert Sedgewick from http://www.cs.princeton.edu/~rs/shell/shell.c

void ShellSort(SortArray& A)
{
    size_t incs[16] = { 1391376, 463792, 198768, 86961, 33936,
                        13776, 4592, 1968, 861, 336,
                        112, 48, 21, 7, 3, 1 };

    for (size_t k = 0; k < 16; k++)
    {
        for (size_t h = incs[k], i = h; i < A.size(); i++)
        {
            value_type v = A[i];
            size_t j = i;

            while (j >= h && A[j-h] > v)
            {
                A.set(j, A[j-h]);
                j -= h;
            }

            A.set(j, v);
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
    volatile ssize_t cycleStart = 0;
    array.watch(&cycleStart, 16);

    volatile ssize_t rank = 0;
    array.watch(&rank, 3);

    // Loop through the array to find cycles to rotate.
    for (cycleStart = 0; cycleStart < n - 1; ++cycleStart)
    {
        value_type& item = array.get_mutable(cycleStart);

        do {
            // Find where to put the item.
            rank = cycleStart;
            for (ssize_t i = cycleStart + 1; i < n; ++i)
            {
                if (array[i] < item)
                    rank++;
            }

            // If the item is already there, this is a 1-cycle.
            if (rank == cycleStart) {
                array.mark(rank, 2);
                break;
            }

            // Otherwise, put the item after any duplicates.
            while (item == array[rank])
                rank++;

            // Put item into right place and colorize
            std::swap(array.get_mutable(rank), item);
            array.mark(rank, 2);

            // Continue for rest of the cycle.
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
