/******************************************************************************
 * src/algorithms/pathological.h
 *
 * Implementations of pathological sorting algorithms.
 *
 * These algorithms are very slow (worse than O(N^2) average case) and should
 * never be used to solve real problems.
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
#include "algorithms/pathological.h"

#include <random>

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
	std::random_device rd;
	std::mt19937 rng(rd());

	// keep a permutation of [0,size)
	std::vector<size_t> perm(A.size());

	for (size_t i = 0; i < A.size(); ++i)
		perm[i] = i;

	while (1)
	{
		// check if array is sorted
		if (BogoCheckSorted(A)) break;

		// pick a random permutation of indexes
		std::shuffle(perm.begin(), perm.end(), rng);

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
	std::random_device rd;
	std::mt19937 rng(rd());
	std::uniform_int_distribution<size_t> uid(0, A.size()-1);

	while (1)
	{
		// check if array is sorted
		if (BogoCheckSorted(A)) break;

		// swap two random items
		A.swap(uid(rng), uid(rng));
	}
}

// ****************************************************************************
// *** BoJo Sort
//
// Dithers around ineffectually, doing the right thing after exhausting all other
// options, or when trapped by the walls closing in.

void BoJoSort(SortArray& A)
{
	size_t redWall = 1, blueWall = A.size()-1;

	std::random_device rd;
	std::mt19937 rng(rd());

	while(redWall <= blueWall) {
		std::uniform_int_distribution<size_t> uid(redWall, blueWall);
		size_t i = uid(rng);

		if(A[i] < A[i-1]) {
			A.swap(i, i-1);

			if(i == redWall && redWall > 1) {
				redWall--;
				A.unmark(redWall-1);
			}
			if(i == blueWall && blueWall < A.size()-1) {
				blueWall++;
				A.unmark(blueWall);
			}
		} else {
			if(i == redWall) {
				A.mark(redWall-1, 7);
				redWall++;
			}
			if(i == blueWall) {
				A.mark(blueWall, 12);
				blueWall--;
			}
		}
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

