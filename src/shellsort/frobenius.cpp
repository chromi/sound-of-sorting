// Routines to explore Frobenius theory.
// (c) 2021 Jonathan Morton <chromatix99@gmail.com>

#include "frobenius.hpp"
#include "sequences.hpp"
#include "analysis.hpp"

extern void analyseDijkstra(const Sequence& seq);

#include <cstring>
#include <random>
#include <algorithm>

static const uint64_t limit = 1ULL << 40;
//static const uint64_t limit = 1ULL << 32;
//static const uint64_t limit = 5000;

void printFrobeniusSet(const Sequence& seq)
{
	std::vector<uint64_t> s = seq.seq;
	DoubleVec lens, costs;

	for(double s=12*4, len=16; len <= limit; s++, len=rint(pow(2, s/12))) {
		lens.push_back(len);
		costs.push_back(0);
	}

	while(s.front() < limit) {
		// CAR and CDR
		uint64_t base = s.front();
		s.erase(s.begin());

		Frobenius f(s, limit);
		printf("%18lu:", base);
		fflush(stdout);

		// std::vector<uint64_t> bruteFS = f.frobeniusSetBruteForce(base, limit);
		std::vector<uint64_t> smartFS = f.frobeniusSet(base, limit);

		printf(" (%lu)", smartFS.size());

		for(size_t i=0, j=0; i < lens.size(); i++) {
			while(j < smartFS.size() && smartFS[j] < lens[i])
				j++;
			costs[i] += j;
		}

		if(smartFS.size() < 10) {
			for(size_t j=0; j < smartFS.size(); j++)
				printf(" %lu", smartFS[j]);
		} else {
			for(size_t j=0; j < 4; j++)
				printf(" %lu", smartFS[j]);
			printf(" ...");
			for(size_t j=smartFS.size()-4; j < smartFS.size(); j++)
				printf(" %lu", smartFS[j]);
		}
		printf("\n");
		fflush(stdout);
	}

//	Curve crv = fitCurve(lens, costs);
//	printf("\tcost = %g * N^%g * ln^%g(N) + %g\n", crv.a, crv.b, crv.c, crv.d);

	for(size_t i=0; i < lens.size(); i++)
		printf("%18.0f: %18.0f\n",      lens[i], costs[i]);
//		printf("%18.0f: %18.0f %18.0f\n", lens[i], costs[i], crv(lens[i]));
}

void compareFrobeniusSets(const Sequence& seq)
{
	std::vector<uint64_t> s = seq.seq;

	while(s.front() < limit) {
		// CAR and CDR
		uint64_t base = s.front();
		s.erase(s.begin());

		Frobenius f(s);
		printf("%18lu:\n", base);
		uint64_t frobenius = f.getFrobenius();

		(void) f.verify();

		for(uint64_t i=0; i < limit/base; i++) {
			uint64_t x = base * (i+1);

			if(x > frobenius)
				break;

			printf("\r\t%18lu:", x);

			bool smartOb = f.isObtainable(x);
			printf(" %c", smartOb ? '-' : 'S');

			bool bruteOb = f.isObtainableBruteForce(x);
			printf(" %c", bruteOb ? '-' : 'B');

			if(smartOb == bruteOb)
				fflush(stdout);
			else
				printf("\n");
		}
		printf("\n");
	}	
}


// -----------------------------------------------------

struct ShellStats {
	std::vector<uint64_t> insertionDepthFreq;
	std::vector<uint64_t> comparisonDepthFreq;
};
typedef std::vector<ShellStats> ShellStatsVec;

template<typename T>
ShellStats instrumentedShellPass(std::vector<T>& A, const size_t gap)
{
	ShellStats out;
	size_t maxDepth = 0, maxComps = 0;

	// account for elements that are at the very end of insertion chains
	out.insertionDepthFreq.push_back(gap);
	out.comparisonDepthFreq.push_back(gap);

	// perform a shell pass
	for(size_t i=gap; i < A.size(); i++) {
		uint64_t comps=1, depth=0;

		if(A[i] < A[i-gap]) {
			const T t = A[i];
			size_t j = i;

			do {
				depth++;
				A[j] = A[j-gap];
				j -= gap;
			} while(j >= gap && comps++ && t < A[j-gap]);

			A[j] = t;
		}

		if(unlikely(depth > maxDepth || comps > maxComps)) {
			maxDepth = std::max(depth, maxDepth);
			maxComps = std::max(comps, maxComps);
			out.insertionDepthFreq.resize(maxDepth+1);
			out.comparisonDepthFreq.resize(maxComps+1);
		}
		out.insertionDepthFreq[depth]++;
		out.comparisonDepthFreq[comps]++;
	}

	return out;
}

template<typename T>
ShellStatsVec instrumentedShellSort(std::vector<T>& A, const Sequence& seq)
{
	ShellStatsVec out;

	out.reserve(seq.seq.size());

	for(size_t i=seq.seq.size(); i > 0; i--)
		if(seq.seq[i-1] < A.size())
			out.push_back(instrumentedShellPass(A, seq.seq[i-1]));

	return out;
}

static const size_t minSamples = 5;

void analyseShell(const Sequence& seq)
{
	static const uint64_t end = 1ULL << 32;
	const std::string filename1 = seq.shortName + ".totals.tsv";
	const std::string filename2 = seq.shortName + ".passes.tsv";

	// start with Frobenius tables of the sequence, valid up to 2^32
	std::vector<Frobenius> frob;
	{
		std::vector<uint64_t> s = seq.seq;

		while(s.front() < end) {
			// CAR and CDR
			uint64_t base = s.front();
			s.erase(s.begin());

			printf(" %lu", base);
			fflush(stdout);
			frob.push_back({s,end});
		}
		printf("\n");
	}

	std::random_device rd;
	std::mt19937 rng(rd());

	FILE* tfp = fopen(filename1.c_str(), "w");
	fprintf(tfp, "length\tmoves\tcomps\n");

	FILE* pfp = fopen(filename2.c_str(), "w");
	fprintf(pfp, "length\tgap\tfrobSet\tmoves\tcomps\tmaxDepth\tdynamic\n");

	// For each array size,
	//   for each Shell pass,
	//     the gap, the Frobenius set, and a list of empirical samples.
	struct StatDump {
		uint64_t              gap;
		std::vector<uint64_t> frobeniusSet;
		ShellStatsVec         samples;
	};
	std::vector<std::vector<StatDump> > stats;

	// start at 16, end at 2^32, 12 per octave, no duplicates
	stats.resize(1 + 12*(32-4));

	for(size_t s=0, ss=12*4; ss <= 12*32; s++,ss++) {
		const uint64_t len = rint(pow(2, ss/12.0));

		printf("%10lu", len);
		fflush(stdout);

		// start by populating the input-invariant data for each pass at this size
		for(int pass = seq.seq.size()-1; pass >= 0; pass--) {
			if(seq.seq[pass] >= len) continue;
			stats[s].push_back({
				seq.seq[pass], frob[pass].frobeniusSet(seq.seq[pass], len), {}
			});
		}

		// now repeatedly generate inputs and run instrumented Shellsorts on them
		// we run more tests on smaller inputs to smooth out statistical outliers
		std::vector<uint32_t> A(len);
		const size_t numSamples = std::max(minSamples, (size_t) ceil(sqrt(end / (double) len)));
		uint64_t moves=0, comps=0, frobs=0;
		std::vector<uint64_t> pMoves, pComps, pDepth, pDynamic;

		// printf(" (%lu samples): ", numSamples);
		// fflush(stdout);

		for(size_t i=0; i < numSamples; i++) {
			// input is a random permutation of distinct integers
			std::iota(A.begin(), A.end(), 0);
			std::shuffle(A.begin(), A.end(), rng);

			ShellStatsVec sv = instrumentedShellSort(A,seq);
			pMoves.resize(sv.size());
			pComps.resize(sv.size());
			pDepth.resize(sv.size());
			pDynamic.resize(sv.size());

			// transfer the stats into the per-pass arrays
			// also calculate overall statistics for immediate printing
			for(size_t j=0; j < sv.size(); j++) {
				stats[s][j].samples.push_back(sv[j]);

				for(size_t k=1; k < sv[j].insertionDepthFreq.size(); k++) {
					uint64_t tMoves = k * sv[j].insertionDepthFreq[k];
					moves += tMoves;
					pMoves[j] += tMoves;
					pDynamic[j] += sv[j].insertionDepthFreq[k];
				}
				for(size_t k=1; k < sv[j].comparisonDepthFreq.size(); k++) {
					uint64_t tComps = k * sv[j].comparisonDepthFreq[k];
					comps += tComps;
					pComps[j] += tComps;
				}

				pDepth[j] = std::max(sv[j].insertionDepthFreq.size() - 1, pDepth[j]);
			}
		}

		printf("\t%.0f\t%.0f\n", moves / (double) numSamples, comps / (double) numSamples);
		for(size_t j=0; j < pMoves.size(); j++) {
			fprintf(pfp, "%lu\t%lu\t%lu\t%.1f\t%.1f\t%lu\t%.1f\n", len, stats[s][j].gap, stats[s][j].frobeniusSet.size(),
				pMoves[j] / (double) numSamples, pComps[j] / (double) numSamples, pDepth[j], pDynamic[j] / (double) numSamples);
			frobs += stats[s][j].frobeniusSet.size();
		}
		fflush(pfp);

		fprintf(tfp, "%lu\t%.1f\t%.1f\t %lu\n", len, moves / (double) numSamples, comps / (double) numSamples, frobs);
		fflush(tfp);
	}

	fclose(tfp);
	fclose(pfp);
}


// -----------------------------------------------------

int main(int argc, char *argv[])
{
	populateSequences();

	if(argc <= 1) {
		for(size_t i=0; i < sequences.size(); i++) {
			const Sequence& seq = sequences[i];
			printf("%s (%s)\n", seq.longName.c_str(), seq.shortName.c_str());

			for(size_t j = 0; j < seq.seq.size(); j++)
				printf(" %lu", seq.seq[j]);
			printf("\n\n");
		}
	} else {
		bool frobenius = false;
		bool benchmark = false;
		bool dijkstra  = false;
		bool custom    = false;

		for(int a=1; a < argc; a++) {
			if(!strcmp(argv[a], "--frobenius")) frobenius = true;
			if(!strcmp(argv[a], "--benchmark")) benchmark = true;
			if(!strcmp(argv[a], "--dijkstra") ) dijkstra  = true;
			if(!strcmp(argv[a], "--custom")   ) custom    = true;
		}

		if(custom) {
			// look for numeric arguments and build a custom Sequence from them
			Sequence seq = { "--custom", "Custom Sequence", {} };
			for(int a=1; a < argc; a++) {
				uint64_t v = strtoull(argv[a], NULL, 0);
				if(v > 0)
					seq.seq.push_back(v);
			}
			std::sort(seq.seq.begin(), seq.seq.end());
			sequences.push_back(seq);
		}

		for(size_t i=0; i < sequences.size(); i++) {
			const Sequence& seq = sequences[i];

			bool proceed = false;
			for(int a = 1; a < argc; a++)
				if(!seq.shortName.compare(argv[a]))
					proceed = true;

			if(proceed) {
				printf("%s (%s)\n", seq.longName.c_str(), seq.shortName.c_str());
				if(frobenius) printFrobeniusSet(seq);
				if(benchmark) analyseShell(seq);
				if(dijkstra)  analyseDijkstra(seq);
				if(!(frobenius | benchmark | dijkstra)) {
					for(size_t j = 0; j < seq.seq.size(); j++)
						printf(" %lu", seq.seq[j]);
					printf("\n\n");
				}
			}
		}
	}

	return 0;
}

