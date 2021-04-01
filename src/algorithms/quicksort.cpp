/******************************************************************************
 * src/algorithms/quicksort.cpp
 *
 * Implementations of quicksort-based sorting algorithms.
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
#include "algorithms/quicksort.h"

#include <random>

// ****************************************************************************
// *** Quick Sort Pivot Selection

QuickSortPivotType g_quicksort_pivot = PIVOT_MEDIAN3;

// Recursive median-of-medians implementation
ssize_t QuickSortMedianMedians(SortArray& A, ssize_t lo, ssize_t hi)
{
	ssize_t log5 = 0, exp5 = 1, exp5_1 = 0;
	ssize_t m[5], n = hi-lo;
	value_type v[5];

	while(exp5 < n) {
		exp5_1 = exp5;
		log5++;
		exp5 *= 5;
	}

	if(log5 < 1)
		return lo;

	// fill indexes, recursing if required
	if(log5 == 1) {
		for(ssize_t i=lo, j=0; i < hi; i++,j++) {
			m[j] = i;
			v[j] = A[i];
		}
	} else {
		n = 0;
		for(ssize_t i=lo; i < hi; i += exp5_1) {
			m[n] = QuickSortMedianMedians(A, i, std::min(hi, i+exp5_1));
			v[n] = A[m[n]];
			n++;
		}
	}

	// sort - insertion sort is good enough for 5 elements
	for(ssize_t i=1; i < n; i++) {
		ssize_t t = m[i];
		const value_type tt = v[i];
		ssize_t j;

		for(j=i; j; j--) {
			if(v[j-1] <= tt)
				break;
			m[j] = m[j-1];
			v[j] = v[j-1];
		}
		if(j < i) {
			m[j] = t;
			v[j] = tt;
		}
	}

	// return median
	return m[(n-1)/2];
}

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

	if (g_quicksort_pivot == PIVOT_MEDIAN3_RANDOM)
	{
		ssize_t s1 = lo + (rand() % (hi - lo));
		ssize_t s2 = lo + (rand() % (hi - lo));
		ssize_t s3 = lo + (rand() % (hi - lo));

		// cases if two are equal
		if (A[s1] == A[s2]) return s1;
		if (A[s1] == A[s3] || A[s2] == A[s3]) return s3;

		// cases if three are different
		return A[s1] < A[s2]
		? (A[s2] < A[s3] ? s2 : (A[s1] < A[s3] ? s3 : s1))
		: (A[s2] > A[s3] ? s2 : (A[s1] < A[s3] ? s1 : s3));
	}

	if (g_quicksort_pivot == PIVOT_MEDIAN_MEDIANS)
	{
		return QuickSortMedianMedians(A, lo, hi);
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
	sl.Add( _("Median of Three Random") );
	sl.Add( _("Median of Medians") );

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

// Rewritten by Jonathan Morton
// Now chooses better pivots for (nearly) sorted inputs, and handles runs of equal values.
// Quadratic behaviour is thus avoided for most common data.

void dualPivotYaroslavskiy(class SortArray& a, int left, int right)
{
	if(right <= left)
		return;	// at most one element, trivially sorted

	if(right == left+1) {
		// exactly two elements, compare and swap
		if(a[left] > a[right])
			a.swap(left, right);
		return;
	}

	const size_t offset = (right - left) / 3;
	value_type p = a[left  + offset];
	value_type q = a[right - offset];
	bool swapped = false;

	if(p > q) {
		std::swap(p,q);
		swapped = true;
	}

	a.mark(left);
	a.mark(right);

	volatile ssize_t l = left;
	volatile ssize_t g = right;
	volatile ssize_t k = l;

	a.watch(&l, 3);
	a.watch(&g, 3);
	a.watch(&k, 3);

	while (k <= g)
	{
		if (a[k] < p) {
			if(k != l)
				a.swap(k, l++);
			else
				l++;
		} else if (a[k] > q) {
			while (k < g && a[g] > q)
				g--;
			if(k < g)
				a.swap(k, g--);
			else
				g--;

			if (a[k] < p)
				a.swap(k, l++);
		}
		k++;
	}

	a.unmark_all();
	a.unwatch_all();

	if(l == left && g == right) {
		// pivots are extrema; no values found above q or below p
		if(p == q)
			return;	// run of equals

		if(offset) {
			if(swapped) {
				a.swap(right - offset, left);
				a.swap(left  + offset, right);
			} else {
				a.swap(left  + offset, left);
				a.swap(right - offset, right);
			}
		} else if(swapped) {
			a.swap(left, right);
		}

		// extrema values moved to ends, so we will make progress
		l++;
		g--;
	}

	if(l > left)
		dualPivotYaroslavskiy(a, left, l - 1);

	if(g > l && p != q)
		dualPivotYaroslavskiy(a, l, g);

	if(g < right)
		dualPivotYaroslavskiy(a, g + 1, right);
}

void QuickSortDualPivot(class SortArray& a)
{
	return dualPivotYaroslavskiy(a, 0, a.size()-1);
}

// ****************************************************************************
// *** IntroSort

// by Jonathan Morton

void IntroSort(class SortArray& A, ssize_t l, ssize_t r, ssize_t expectedDepth)
{
	// Small subarrays get insertion sorted.
	if(r <= l + 16) {
		for(ssize_t i = l+1; i < r; i++) {
			ssize_t j;

			for(j = i-1; j >= l; j--)
				if(A[j] <= A[i])
					break;
			A.rotate(j+1, i, i+1);
		}

		// Mark as completely sorted.
		for(ssize_t i = l; i < r; i++)
			A.mark(i, 2);
		return;
	}

	// Main body of sort is a competent ternary quicksort.  We allow the user to select the default pivot strategy.
	// However, if we recurse more than log2(N) levels, we switch to the slower but more reliable median-of-medians.
	ssize_t p = (expectedDepth >= r-l) ? QuickSortSelectPivot(A, l, r) : QuickSortMedianMedians(A, l, r);
	const value_type pivot = A[p];

	// We don't unconditionally move the pivot value anywhere.
	// If it's out of position, it'll be corrected by the partitioning pass.
	// That will also mark the value as "equal to the pivot".
	// So we just mark it (and the block boundaries) once and forget about where we found it.
	A.mark(l,   3);
	A.mark(r-1, 3);
	A.mark(p,   6);

	// Ternary partitioning pass, leaving small values at left, large values at right, and pivot values in middle.
	// Shamelessly ripped from Yaroslavskiy dual-pivot, above, and adapted to suit.
	ssize_t i=l, j=l, k=r-1;

	while(j <= k) {
		const value_type v = A[j];
		const int cv = v.cmp(pivot);

		if(cv < 0) {
			A.mark(j, 3);
			A.swap(i++, j++, true);
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
			A.swap(j, k);
			A.mark(k--, 3);

			if(cw < 0) {
				A.mark(j, 3);
				A.swap(i++, j++, true);
			} else {
				A.mark(j++, 6);
			}
		} else {
			A.mark(j++, 6);
		}
	}
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
	expectedDepth = (expectedDepth * 3) / 4;

	if(i-l < r-k) {
		IntroSort(A, l, i, expectedDepth);
		IntroSort(A, k, r, expectedDepth);
		return;
	} else {
		IntroSort(A, k, r, expectedDepth);
		IntroSort(A, l, i, expectedDepth);
		return;
	}
}

void IntroSort(class SortArray& A)
{
	IntroSort(A, 0, A.size(), A.size());
}

// ****************************************************************************
// *** Dual-Pivot IntroSort

// by Jonathan Morton

#include "algorithms/heap.h"

typedef struct {
	size_t l,r;
} SortRange;

typedef struct {
	size_t a,b,c;
} PartitionCounts3;

void TernaryPartitionMerge(class SortArray& A, const SortRange& p,
		size_t a, size_t b, size_t c, size_t aa, size_t bb, size_t cc)
{
	assert(a+b+c + aa+bb+cc == p.r - p.l);

	if(b + bb > c + aa) {
		A.rotate(p.l + a + b, p.l + a + b + c, p.l + a + b + c + aa);
		A.rotate(p.l + a, p.l + a + b, p.l + a + b + aa);
		A.rotate(p.r - cc - bb - c, p.r - cc - bb, p.r - cc);
	} else {
		A.rotate(p.l + a, p.l + a + b + c, p.r - cc);
		A.rotate(p.l + a + aa, p.l + a + aa + bb, p.r - cc - c);
	}
}

PartitionCounts3 DualStablePartition(class SortArray& A, const SortRange& p,
		const value_type& pB, const value_type& pD)
{
	PartitionCounts3 op = {0,0,0};
	assert(p.r > p.l);

	if(p.r - p.l == 1) {
		// Single item, compare against pivots, classify and mark
		const value_type v = A[p.l];

		if(v <= pB) {
			op.a++;
			A.mark(p.l, 3);
		} else if(v >= pD) {
			op.c++;
			A.mark(p.l, 3);
		} else {
			op.b++;
			A.mark(p.l, 5);
		}
		return op;
	}

	// Recursively partition halves
	const size_t mid = (p.l + p.r) / 2;
	const SortRange lh = { p.l, mid }, rh = { mid, p.r };
	const PartitionCounts3 lp = DualStablePartition(A, lh, pB, pD);
	const PartitionCounts3 rp = DualStablePartition(A, rh, pB, pD);

	// Stable partition merge: abcABC -> aAbBcC
	TernaryPartitionMerge(A, p, lp.a, lp.b, lp.c, rp.a, rp.b, rp.c);

	// Return merged partition sizes
	op.a = lp.a + rp.a;
	op.b = lp.b + rp.b;
	op.c = lp.c + rp.c;
	return op;
}

PartitionCounts3 TernaryStablePartition(class SortArray& A, const SortRange& p,
		const value_type& pB)
{
	PartitionCounts3 op = {0,0,0};
	assert(p.r > p.l);

	if(p.r - p.l == 1) {
		// Single item, compare against pivots, classify and mark
		const value_type v = A[p.l];
		const int c = v.cmp(pB);

		if(c < 0) {
			op.a++;
			A.mark(p.l, 3);
		} else if(c > 0) {
			op.c++;
			A.mark(p.l, 3);
		} else {
			op.b++;
			A.mark(p.l, 6);
		}
		return op;
	}

	// Recursively partition halves
	const size_t mid = (p.l + p.r) / 2;
	const SortRange lh = { p.l, mid }, rh = { mid, p.r };
	const PartitionCounts3 lp = TernaryStablePartition(A, lh, pB);
	const PartitionCounts3 rp = TernaryStablePartition(A, rh, pB);

	// Stable partition merge: abcABC -> aAbBcC
	TernaryPartitionMerge(A, p, lp.a, lp.b, lp.c, rp.a, rp.b, rp.c);

	// Return merged partition sizes
	op.a = lp.a + rp.a;
	op.b = lp.b + rp.b;
	op.c = lp.c + rp.c;
	return op;
}

void IntroSortDual(class SortArray& A, bool stable)
{
	// pivot selection relies on good-quality random sampling
	std::random_device rngd;
	std::default_random_engine rng(rngd());

	// use a priority queue to run small partitions first
	// initialise it with the full array
	std::vector<SortRange> q;
	{
		SortRange full = { 0, A.size() };
		q.push_back(full);
	}

	while(!q.empty()) {
		const SortRange p = q.back();
		q.pop_back();

		if(p.r - p.l < 32) {
			// small partition
			SplaySort(A, p.l, p.r);

			// Mark as completely sorted.
			for(size_t i = p.l; i < p.r; i++)
				A.mark(i, 2);

			continue;
		}

		// select two pivots as the 2nd & 4th ranks of five random samples
		std::uniform_int_distribution<size_t> sampler(p.l, p.r-1);
		size_t si[5];
		for(int i=0; i < 5; i++) {
			si[i] = sampler(rng);

			// insertion-sort to keep samples in sorted order
			// note that samples may occasionally land on same index, so avoid unnecessary compares
			for(int j = i; j > 0; j--) {
				if(si[j] != si[j-1] && A[si[j]] < A[si[j-1]])
					std::swap(si[j], si[j-1]);
				else
					break;
			}
		}
		const value_type pB = A[si[1]], pD = A[si[3]];
		A.mark(si[1], 6);
		A.mark(si[3], 6);

		// perform (stable?) partition into three around two pivots
		PartitionCounts3 parts = {0,0,0};
		bool ternary = (pB == pD);

		if(stable) {
			if(ternary)
				parts = TernaryStablePartition(A, p, pB);
			else
				parts = DualStablePartition(A, p, pB, pD);
		} else if(ternary) {
			// we probably have a run of values equal to the pivot
			// so we'll perform a ternary partitioning: [ A < p == B == q < C ]
			size_t i = p.l, j = p.l, k = p.r-1;

			while(j <= k) {
				const value_type v = A[j];
				const int cv = v.cmp(pB);

				if(cv < 0) {
					A.mark(j, 3);
					A.swap(i++, j++, true);
				} else if(cv > 0) {
					value_type w;
					int cw;
					do {
						w = A[k];
						cw = w.cmp(pB);
						if(cw > 0)
							A.mark(k--, 3);
					} while(cw > 0);

					if(j > k)
						break;
					A.swap(j, k);
					A.mark(k--, 3);

					if(cw < 0) {
						A.mark(j, 3);
						A.swap(i++, j++, true);
					} else {
						A.mark(j++, 6);
					}
				} else {
					A.mark(j++, 6);
				}
			}
			k++;

			parts.a = i - p.l;
			parts.b = k - i;
			parts.c = p.r - k;
		} else {
			// perform a dual-pivot three-way partitioning: [ A <= p < B < q <= C ]
			size_t i = p.l, j = p.l, k = p.r-1;

			while(j <= k) {
				const value_type v = A[j];

				if(v <= pB) {
					A.mark(j, 3);
					A.swap(i++, j++, true);
				} else if(v >= pD) {
					value_type w;

					while((w = A[k]) >= pD)
						A.mark(k--, 3);

					if(j > k)
						break;
					A.swap(j, k);
					A.mark(k--, 3);

					if(w <= pB) {
						A.mark(j, 3);
						A.swap(i++, j++, true);
					} else {
						A.mark(j++, 5);
					}
				} else {
					A.mark(j++, 5);
				}
			}
			k++;

			parts.a = i - p.l;
			parts.b = k - i;
			parts.c = p.r - k;
		}
		assert(parts.a + parts.b + parts.c == p.r - p.l);

		// mark pivot values as completely sorted, unmark others
		if(ternary) {
			size_t x = p.l;
			for(size_t y = parts.a; y > 0; y--)
				A.unmark(x++);
			for(size_t y = parts.b; y > 0; y--)
				A.mark(x++, 2);
			for(size_t y = parts.c; y > 0; y--)
				A.unmark(x++);
		} else {
			for(size_t y = p.l; y < p.r; y++)
				A.unmark(y);
		}

		SortRange pp = { p.l, p.l + parts.a };
		if(parts.a) {
			q.push_back(pp);
			for(size_t j = q.size()-1; j > 0; j--) {
				if(q[j-1].r - q[j-1].l < parts.a)
					std::swap(q[j-1], q[j]);
				else
					break;
			}
		}
		if(!ternary) {
			pp.l = pp.r;
			pp.r = pp.l + parts.b;
			if(parts.b) {
				q.push_back(pp);
				for(size_t j = q.size()-1; j > 0; j--) {
					if(q[j-1].r - q[j-1].l < parts.b)
						std::swap(q[j-1], q[j]);
					else
						break;
				}
			}
		}
		pp.l = p.l  + parts.b + parts.a;
		pp.r = pp.l + parts.c;
		if(parts.c) {
			q.push_back(pp);
			for(size_t j = q.size()-1; j > 0; j--) {
				if(q[j-1].r - q[j-1].l < parts.c)
					std::swap(q[j-1], q[j]);
				else
					break;
			}
		}
		assert(pp.r == p.r);
	}
}

void IntroSortDual(class SortArray& A) { IntroSortDual(A, false); }

void IntroSortDualStable(class SortArray& A) { IntroSortDual(A, true); }

// ****************************************************************************
// *** Septenary Stable Quicksort

// by Jonathan Morton

typedef struct {
	size_t a,b,c,d,e,f,g;
} PartitionCounts7;

PartitionCounts7 SeptenaryPartition(class SortArray& A, const SortRange& p,
		const value_type& pB, const value_type& pD, const value_type& pF)
{
	PartitionCounts7 op = {0,0,0,0,0,0,0};
	assert(p.r > p.l);

	const size_t m = (p.r + p.l) / 2;
	SortRange rB = { p.l, p.l }, rD = { m, m }, rF = { p.r, p.r };	// borders of equal-to-pivot partitions
	size_t i=m, j=m;	// leading edges (from centre) of C and E partitions, trailing edges of open partitions
	value_type vi = A[i-1], vj = A[j];
	int cDi = vi.cmp(pD);
	int cDj = vj.cmp(pD);

	while(i > rB.r && j < rF.l) {
		// Both sides are open, find pair of elements on wrong sides and swap them
		// Elements on correct side are moved behind correct leading edge on that side

		// First check for equality with middle pivot
		while(cDi == 0) {
			A.mark(--i, 6);
			A.swap(i, --rD.l, true);
			if(i <= rB.r)
				break;
			vi = A[i-1];
			cDi = vi.cmp(pD);
		}
		while(cDj == 0) {
			A.mark(j, 6);
			A.swap(j++, rD.r++, true);
			if(j >= rF.l)
				break;
			vj = A[j];
			cDj = vj.cmp(pD);
		}

		// Deal with left-side elements on correct side
		while(cDi < 0) {
			int cB = vi.cmp(pB), cBB = 0;

			while(cB <= 0 && i > rB.r+1 && (cBB = A[rB.r].cmp(pB)) <= 0) {
				// Extend left partitions
				if(cBB < 0) {
					A.mark(rB.r, 3);
					A.swap(rB.r++, rB.l++, true);
				} else {
					A.mark(rB.r++, 6);
				}
			}

			if(cB < 0) {
				A.mark(--i, 3);
				A.swap3(i++, rB.r++, rB.l++, true);
			} else if(cB > 0) {
				A.mark(--i, 3);
			} else {
				A.mark(--i, 6);
				A.swap(i++, rB.r++, true);
			}

			if(i <= rB.r)
				break;
			vi = A[i-1];
			cDi = vi.cmp(pD);
		}

		// Deal with right-side elements on correct side
		while(cDj > 0) {
			int cF = vj.cmp(pF), cFF = 0;

			while(cF >= 0 && j+1 < rF.l && (cFF = A[rF.l-1].cmp(pF)) >= 0) {
				// Extend right partitions
				if(cFF > 0) {
					A.mark(--rF.l, 3);
					A.swap(rF.l, --rF.r, true);
				} else {
					A.mark(--rF.l, 6);
				}
			}

			if(cF < 0) {
				A.mark(j++, 3);
			} else if(cF > 0) {
				A.mark(j, 3);
				A.swap3(j, --rF.l, --rF.r, true);
			} else {
				A.mark(j, 6);
				A.swap(j, --rF.l, true);
			}

			if(j >= rF.l)
				break;
			vj = A[j];
			cDj = vj.cmp(pD);
		}

		// Swap elements if both are on wrong side
		if(cDi > 0 && cDj < 0) {
			A.swap(i-1, j);
			std::swap(vi, vj);
			std::swap(cDi, cDj);
		}
	}

	while(i > rB.r) {
		// Only the left side is open
		if(cDi < 0) {
			int cB = vi.cmp(pB), cBB = 0;

			while(cB <= 0 && i > rB.r+1 && (cBB = A[rB.r].cmp(pB)) <= 0) {
				// Extend left partitions
				if(cBB < 0) {
					A.mark(rB.r, 3);
					A.swap(rB.r++, rB.l++, true);
				} else {
					A.mark(rB.r++, 6);
				}
			}

			if(cB < 0) {
				A.mark(--i, 3);
				A.swap3(i++, rB.r++, rB.l++, true);
			} else if(cB > 0) {
				A.mark(--i, 3);
			} else {
				A.mark(--i, 6);
				A.swap(i++, rB.r++, true);
			}
		} else if(cDi > 0) {
			int cF = vi.cmp(pF);

			if(cF < 0) {
				A.mark(--i, 3);
				A.swap3(i, --rD.l, --rD.r, true);
			} else if(cF > 0) {
				A.mark(--i, 3);
				A.swap5(i, --rD.l, --rD.r, --rF.l, --rF.r, true);
			} else {
				A.mark(--i, 6);
				A.swap4(i, --rD.l, --rD.r, --rF.l, true);
			}
		} else {
			A.mark(--i, 6);
			A.swap(i, --rD.l, true);
		}

		if(i <= rB.r)
			break;
		vi = A[i-1];
		cDi = vi.cmp(pD);
	}

	while(j < rF.l) {
		// Only the right side is open
		if(cDj < 0) {
			int cB = vj.cmp(pB);

			if(cB < 0) {
				A.mark(j, 3);
				A.swap5(j++, rD.r++, rD.l++, rB.r++, rB.l++, true);
			} else if(cB > 0) {
				A.mark(j, 3);
				A.swap3(j++, rD.r++, rD.l++, true);
			} else {
				A.mark(j, 6);
				A.swap4(j++, rD.r++, rD.l++, rB.r++, true);
			}
		} else if(cDj > 0) {
			int cF = vj.cmp(pF), cFF = 0;

			while(cF >= 0 && j+1 < rF.l && (cFF = A[rF.l-1].cmp(pF)) >= 0) {
				// Extend right partitions
				if(cFF > 0) {
					A.mark(--rF.l, 3);
					A.swap(rF.l, --rF.r, true);
				} else {
					A.mark(--rF.l, 6);
				}
			}

			if(cF < 0) {
				A.mark(j++, 3);
			} else if(cF > 0) {
				A.mark(j, 3);
				A.swap3(j, --rF.l, --rF.r, true);
			} else {
				A.mark(j, 6);
				A.swap(j, --rF.l, true);
			}
		} else {
			A.mark(j, 6);
			A.swap(j++, rD.r++, true);
		}

		if(j >= rF.l)
			break;
		vj = A[j];
		cDj = vj.cmp(pD);
	}

	ASSERT(i <= rB.r);
	ASSERT(i <= rD.l);
	ASSERT(j >= rD.r);
	ASSERT(j >= rF.l);

	ASSERT(rB.l >= p.l);
	ASSERT(rB.r >= rB.l);
	ASSERT(rD.l >= rB.r);
	ASSERT(rD.r >= rD.l);
	ASSERT(rF.l >= rD.r);
	ASSERT(rF.r >= rF.l);
	ASSERT(p.r  >= rF.r);

	op.a = rB.l - p.l;
	op.b = rB.r - rB.l;
	op.c = rD.l - rB.r;
	op.d = rD.r - rD.l;
	op.e = rF.l - rD.r;
	op.f = rF.r - rF.l;
	op.g = p.r  - rF.r;
	return op;
}

PartitionCounts7 SeptenaryStablePartition(class SortArray& A, const SortRange& p,
		const value_type& pB, const value_type& pD, const value_type& pF)
{
	PartitionCounts7 op = {0,0,0,0,0,0,0};
	assert(p.r > p.l);

	if(p.r - p.l == 1) {
		// Single item, compare against pivots, classify and mark
		int cD = A[p.l].cmp(pD);

		if(cD < 0) {
			int cB = A[p.l].cmp(pB);

			if(cB < 0) {
				op.a++;
				A.mark(p.l, 3);
			} else if(cB > 0) {
				op.c++;
				A.mark(p.l, 3);
			} else {
				op.b++;
				A.mark(p.l, 6);
			}
		} else if(cD > 0) {
			int cF = A[p.l].cmp(pF);

			if(cF < 0) {
				op.e++;
				A.mark(p.l, 3);
			} else if(cF > 0) {
				op.g++;
				A.mark(p.l, 3);
			} else {
				op.f++;
				A.mark(p.l, 6);
			}
		} else {
			op.d++;
			A.mark(p.l, 6);
		}
		return op;
	}

	// Recursively partition halves
	const size_t mid = (p.l + p.r) / 2;
	const SortRange lh = { p.l, mid }, rh = { mid, p.r };
	const PartitionCounts7 lp = SeptenaryStablePartition(A, lh, pB, pD, pF);
	const PartitionCounts7 rp = SeptenaryStablePartition(A, rh, pB, pD, pF);

	// Stable partition merge: abcdefgABCDEFG -> aAbBcCdDeEfFgG
	// Perform as three abcABC -> aAbBcC merges using two or three block rotations each
	// Choice of two merge strategies at each stage to minimise data movement:
	// 1: abcABC -> abAcBC -> aAbBcC - if len(bB)  > len(cA), moves c and A twice
	// 2: abcABC -> aABbcC -> aAbBcC - if len(bB) <= len(cA), moves b and B twice

	// First, merge abc-d-efg with ABC-D-EFG:
	size_t lHead = lp.a + lp.b + lp.c;
	size_t lTail = lp.e + lp.f + lp.g;
	size_t rHead = rp.a + rp.b + rp.c;
	size_t rTail = rp.e + rp.f + rp.g;

	TernaryPartitionMerge(A, p, lHead, lp.d, lTail, rHead, rp.d, rTail);

	// Next, merge abc with ABC:
	size_t lPart = lHead + rHead;
	SortRange lRange = { p.l, p.l + lPart };

	TernaryPartitionMerge(A, lRange, lp.a, lp.b, lp.c, rp.a, rp.b, rp.c);

	// Finally, merge efg with EFG:
	size_t rPart = lTail + rTail;
	SortRange rRange = { p.r - rPart, p.r };

	TernaryPartitionMerge(A, rRange, lp.e, lp.f, lp.g, rp.e, rp.f, rp.g);

	// Return merged partition sizes
	op.a = lp.a + rp.a;
	op.b = lp.b + rp.b;
	op.c = lp.c + rp.c;
	op.d = lp.d + rp.d;
	op.e = lp.e + rp.e;
	op.f = lp.f + rp.f;
	op.g = lp.g + rp.g;
	return op;
}

void SeptenaryQuickSort(class SortArray& A, bool stable)
{
	// pivot selection relies on good-quality random sampling
	std::random_device rngd;
	std::default_random_engine rng(rngd());

	// use a priority queue to run small partitions first
	// initialise it with the full array
	std::vector<SortRange> q;
	{
		SortRange full = { 0, A.size() };
		q.push_back(full);
	}

	while(!q.empty()) {
		const SortRange p = q.back();
		q.pop_back();

		if(p.r - p.l < 32) {
			// small partition
			SplaySort(A, p.l, p.r);

			// Mark as completely sorted.
			for(size_t i = p.l; i < p.r; i++)
				A.mark(i, 2);

			continue;
		}

		// select three pivots as the 2nd, 4th, 6th ranks of seven random samples
		std::uniform_int_distribution<size_t> sampler(p.l, p.r-1);
		size_t si[7];
		for(int i=0; i < 7; i++) {
			si[i] = sampler(rng);

			// insertion-sort to keep samples in sorted order
			// note that samples may occasionally land on same index, so avoid unnecessary compares
			for(int j = i; j > 0; j--) {
				if(si[j] != si[j-1] && A[si[j]] < A[si[j-1]])
					std::swap(si[j], si[j-1]);
				else
					break;
			}
		}
		const value_type pB = A[si[1]], pD = A[si[3]], pF = A[si[5]];
		A.mark(si[1], 6);
		A.mark(si[3], 6);
		A.mark(si[5], 6);

		// perform (stable?) partition into seven around three pivots
		PartitionCounts7 parts = stable ?
			SeptenaryStablePartition(A, p, pB, pD, pF) :
			SeptenaryPartition      (A, p, pB, pD, pF);
		assert(parts.a + parts.b + parts.c + parts.d + parts.e + parts.f + parts.g == p.r - p.l);

		// mark pivot values as completely sorted, unmark others
		size_t x = p.l;
		for(size_t y = parts.a; y > 0; y--)
			A.unmark(x++);
		for(size_t y = parts.b; y > 0; y--)
			A.mark(x++, 2);
		for(size_t y = parts.c; y > 0; y--)
			A.unmark(x++);
		for(size_t y = parts.d; y > 0; y--)
			A.mark(x++, 2);
		for(size_t y = parts.e; y > 0; y--)
			A.unmark(x++);
		for(size_t y = parts.f; y > 0; y--)
			A.mark(x++, 2);
		for(size_t y = parts.g; y > 0; y--)
			A.unmark(x++);

		// add four open partitions to the queue in sorted order
		// these will all be smaller than the partition just removed from the queue
		// so the time cost of this insertion is no more than insertion sort on 4 items
		SortRange pp = { p.l, p.l + parts.a };
		if(parts.a) {
			q.push_back(pp);
			for(size_t j = q.size()-1; j > 0; j--) {
				if(q[j-1].r - q[j-1].l < parts.a)
					std::swap(q[j-1], q[j]);
				else
					break;
			}
		}
		pp.l = pp.r + parts.b;
		pp.r = pp.l + parts.c;
		if(parts.c) {
			q.push_back(pp);
			for(size_t j = q.size()-1; j > 0; j--) {
				if(q[j-1].r - q[j-1].l < parts.c)
					std::swap(q[j-1], q[j]);
				else
					break;
			}
		}
		pp.l = pp.r + parts.d;
		pp.r = pp.l + parts.e;
		if(parts.e) {
			q.push_back(pp);
			for(size_t j = q.size()-1; j > 0; j--) {
				if(q[j-1].r - q[j-1].l < parts.e)
					std::swap(q[j-1], q[j]);
				else
					break;
			}
		}
		pp.l = pp.r + parts.f;
		pp.r = pp.l + parts.g;
		if(parts.g) {
			q.push_back(pp);
			for(size_t j = q.size()-1; j > 0; j--) {
				if(q[j-1].r - q[j-1].l < parts.g)
					std::swap(q[j-1], q[j]);
				else
					break;
			}
		}
		assert(pp.r == p.r);
	}
}

void SeptenaryQuickSort(class SortArray& A) { SeptenaryQuickSort(A, false); }

void SeptenaryStableQuickSort(class SortArray& A) { SeptenaryQuickSort(A, true); }

