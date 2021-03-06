/******************************************************************************
 * src/algorithms/merge.h
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

// conventional out-of-place mergesorts
void MergeSort(class SortArray& a);
void MergeSortIterative(class SortArray& a);

// in-place "rotation" mergesorts
void MergeSortInPlace(class SortArray& a);
void MergeSortSemiInPlace(class SortArray& a);
void CataMergeSort(class SortArray& a);
void CataMergeSortStable(class SortArray& a);
void SplayMergeSort(class SortArray& a);

// in-place "bitonic" mergesorts
void BitonicMergeRecursive(SortArray& a);
void BitonicMergeIterative(SortArray& a);
void BitonicCataMerge(SortArray& a);
void BitonicSplayMerge(SortArray& a);

// in-place block merges, in blockmerge.cpp
void BlockMergeIterative(SortArray& a);

// the following are not in merge.cpp but have their own implementation files
void TimSort(class SortArray& a);
void WikiSort(class SortArray& a);

void StlStableSort(class SortArray& a);
