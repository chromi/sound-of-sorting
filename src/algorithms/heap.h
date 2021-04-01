/******************************************************************************
 * src/algorithms/heap.h
 *
 * Implementations of heap- and tree-based sorting algorithms.
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

void HeapSort(class SortArray& a);
void SmoothSort(class SortArray& a);

void SplaySort(class SortArray& a);
void SplaySort(class SortArray& A, size_t l, size_t r);
void SplayShakeSort(class SortArray& a);
void SplayShakeSort(class SortArray& a, size_t m);

std::vector<size_t> SplayCollectRuns(SortArray& A, size_t m = 32);

void StlHeapSort(class SortArray& a);
