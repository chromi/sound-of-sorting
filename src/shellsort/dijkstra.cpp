#include "sequences.hpp"

extern void analyseDijkstra(const Sequence& seq);

#include <vector>
#include <boost/dynamic_bitset.hpp>

std::vector<size_t> dijkstra(const size_t len, const Sequence& seq)
{
	boost::dynamic_bitset reached(len), cur(len), next(len);
	std::vector<size_t> steps;

	// mark one element as the origin of all paths
	reached[0] = true;
	cur[0] = true;
	steps.push_back(1);

	printf("%10lu\t1", len);
	fflush(stdout);

	while(!reached.all()) {
		// iterate over leaf nodes
		for(size_t i = cur.find_first(); i < len; i = cur.find_next(i)) {
			for(size_t j=0; j < seq.seq.size(); j++) {
				// step both forward and backward, but not beyond the array limits
				// cull locations we've already reached
				const uint64_t gap = seq.seq[j];
				if(gap >= len) continue;
				if(i >= gap && !reached[i-gap])
					next[i-gap] = true;
				if(len-gap > i && !reached[i+gap])
					next[i+gap] = true;
			}
		}
		steps.push_back(next.count());
		reached |= next;
		cur.swap(next);
		next.reset();

		printf("\t%lu", steps.back());
		fflush(stdout);
	}

	printf("\n");
	return steps;
}

void analyseDijkstra(const Sequence& seq)
{
	const std::string filename1 = seq.shortName + ".paths.tsv";
	FILE* fp = fopen(filename1.c_str(), "w");

	fprintf(fp, "length\tmean\tmedian\tmaximum\tmeanplus\n");

	for(size_t s=0, ss=12*4; ss <= 12*32; s++,ss++) {
		const uint64_t len = rint(pow(2, ss/12.0));

		std::vector<size_t> steps = dijkstra(len, seq);

		uint64_t totalPath = 0, rank = 0, median = 0;

		for(size_t i=0; i < steps.size(); i++) {
			totalPath += steps[i] * i;
			if(rank < len/2) {
				rank += steps[i];
				median = i;
			}
		}

		double mean = totalPath / (double) len;
		double overhead = 0;

		for(size_t i=0; i < seq.seq.size(); i++)
			if(seq.seq[i] < len)
				overhead += (len - seq.seq[i]) / (double) len;

		fprintf(fp, "%lu\t%.4f\t%lu\t%lu\t%.4f\n", len, mean, median, steps.size()-1, mean + overhead);
		fflush(fp);
	}
	fclose(fp);
}
