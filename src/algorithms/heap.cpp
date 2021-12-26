/******************************************************************************
 * src/algorithms/heap.cpp
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

#include "SortAlgo.h"
#include "algorithms/heap.h"

// ****************************************************************************
// *** Heap Sort

// heavily adapted from http://www.codecodex.com/wiki/Heapsort

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
// *** Smooth Sort

namespace SmoothSortNS {

// 64-bit version of count-trailing-zeroes function
static uint8_t ctz64(uint64_t x)
{
	if(x & 1) return 0;
	if(!x)    return 64;

	if(x & 0xFFFFFFFF)
		return __builtin_ctz((uint32_t) x);
	else
		return __builtin_ctz((uint32_t) (x >> 32)) + 32;
}

static const uint64_t one = 1;
static uint64_t LP[65] = { 0 };

static void sift(SortArray& A, uint8_t order, size_t head)
{
	if(order < 2)
		return;

	// Improved sift function to use two comparisons per step, not three
	while(order > 1)
	{
		const size_t rt = head - 1;
		const size_t lf = rt - LP[order-2];

		if(A[lf] < A[rt]) {
			// sift into right child
			if (A[rt] > A[head])
				A.swap(head, rt);
			else
				break;
			head = rt;
			order -= 2;
		} else {
			// sift into left child
			if (A[lf] > A[head])
				A.swap(head, lf);
			else
				break;
			head = lf;
			order -= 1;
		}
	}
}

static void trinkle(SortArray& A, uint64_t heaps, size_t head)
{
	while(heaps) {
		const uint8_t order = ctz64(heaps);

		// leftmost heap has no stepson, just sift
		if((heaps >> order) == one) {
			sift(A, order, head);
			return;
		}

		const size_t stepson = head - LP[order];

		if(A[head] < A[stepson]) {
			if(order > 1) {
				// check stepson against children
				const size_t rt = head - 1;
				const size_t lf = rt - LP[order-2];

				if (A[lf] < A[rt]) {
					// compare head, stepson, and right child
					if(A[stepson] < A[rt]) {
						// by transitive property, A[head] < A[stepson] < A[rt], thus A[head] < A[rt]
						// sift into right child
						A.swap(head, rt);
						sift(A, order-2, rt);
						return;
					}
				} else {
					// compare head, stepson, and left child
					if(A[stepson] < A[lf]) {
						// by transitive property, A[head] < A[stepson] < A[lf], thus A[head] < A[lf]
						// sift into left child
						A.swap(head, lf);
						sift(A, order-1, lf);
						return;
					}
				}
			}

			// move to next root on left
			A.swap(head, stepson);
			head = stepson;

			heaps &= ~(one << order);
		} else {
			// sift into current tree
			sift(A, order, head);
			return;
		}
	}
}

static void semitrinkle(SortArray& A, const uint64_t heaps, const size_t head)
{
	// Semitrinkle assumes the current heap is fully valid, but the root may need to be moved left
	const uint8_t order = ctz64(heaps);

	// leftmost heap has no stepson, just return
	if((heaps >> order) == one)
		return;

	const size_t stepson = head - LP[order];

	if(A[head] < A[stepson]) {
		A.swap(head, stepson);

		if(order == 0 && (heaps & 2))
			semitrinkle(A, heaps & ~one, stepson);	// next one is order 1
		else
			trinkle(A, heaps & ~(one << order), stepson);
	}
}

void sort(SortArray& A, const size_t l, const size_t r)
{
	if(!LP[0]) {
		// Memoise Leonardo numbers
		LP[0] = LP[1] = 1;
		for(size_t i=2; i < 65; i++)
			LP[i] = LP[i-1] + LP[i-2] + 1;
	}
	if(r-l >= LP[64])
		throw;	// limit is somewhere between 34*10^12 and 2^45 - increase the size of bitvector if you *really* need to

	uint64_t heaps = 0; // bitmap of complete Leonardo heap orders

	// Start by building the forest of heaps
	for(size_t head = l; head < r; head++) {
		const uint8_t order = ctz64(heaps);

		if(((heaps >> order) & 3) == 3) {
			// Rightmost heaps are of consecutive order, so merge them
			heaps += one << order;
			sift(A, order+2, head);

			for(size_t i = head, j = LP[order+2]; j--; i--)
				A.mark(i, order+6);
		} else {
			// adding a new block of length 1
			if (heaps & 2) {
				// L(1) already present, so this must be L(0) sibling
				heaps |= one;
				A.mark(head, 4);
			} else {
				// L(1) takes priority over L(0)
				heaps |= one << 1;
				A.mark(head, 5);
			}
		}
	}

	// Sort the root nodes
	for(size_t head = l, order = 63; head < r; order--) {
		if(heaps & (one << order)) {
			uint64_t forest = heaps & ~((one << order) - 1);
			head += LP[order];
			semitrinkle(A, forest, head-1);
		}
	}

	// Now extract one element at a time
	for(size_t head = r-1; head > l; head--) {
		const uint8_t order = ctz64(heaps);

		if(order < 2) {
			// L(0) and L(1) are trivial
			A.mark(head, 2);
			heaps = (heaps - one) & ~one;
		} else {
			// Split L(k) heap into L(k-1) | L(k-2) | head
			size_t i = head, j = LP[order-1], k = LP[order-2];

			A.mark(i--, 2);
			while(k--)
				A.mark(i--, order+2);
			while(j--)
				A.mark(i--, order+3);

			const size_t rt = head - 1, lf = rt - LP[order-2];

			// Ensure roots are in sorted order
			heaps -= one << (order-1);
			semitrinkle(A, heaps, lf);
			heaps += one << (order-2);
			semitrinkle(A, heaps, rt);

		}
	}
	A.mark(l, 2);
}

} // namespace SmoothSortNS

void SmoothSort(SortArray& A)
{
	return SmoothSortNS::sort(A, 0, A.size());
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
	void shake(SortArray& A, size_t l, size_t r, size_t m = 256) {
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
	std::vector<size_t> runs(SortArray& A, size_t m = 256) {
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

std::vector<size_t> SplayCollectRuns(SortArray& A, size_t m)
{
	return Splay::runs(A, m);
}
