/******************************************************************************
 * src/algorithms/parallel.cpp
 *
 * Implementations of sorting algorithms intended for parallel processors.
 *
 * The machine model here is not a parallel processor, so the performance of
 * these algorithms is not representative.
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
#include "algorithms/parallel.h"

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

