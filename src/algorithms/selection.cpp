/******************************************************************************
 * src/algorithms/selection.h
 *
 * Implementations of selection sorting algorithms.
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
#include "algorithms/selection.h"

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
// *** Surprise Sort

// Adapted from https://arxiv.org/abs/2110.01111
// Stanley Fung, "Is this the simplest (and most surprising) sorting algorithm ever?", 2021

// algorithm 1
void SurpriseSort(SortArray& A)
{
	for(size_t i=0; i < A.size(); i++)
		for(size_t j=0; j < A.size(); j++)
			if(A[i] < A[j])
				A.swap(i,j);
}

// algorithm 3
void SurpriseInsertionSort(SortArray& A)
{
	for(size_t i=1; i < A.size(); i++)
		for(size_t j=0; j < i; j++)
			if(A[i] < A[j])
				A.swap(i,j);
}

