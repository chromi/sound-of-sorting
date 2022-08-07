#pragma once

#include <string>
#include <vector>
#include <stdint.h>

typedef struct {
	const std::string shortName, longName;
	std::vector<uint64_t> seq;	// in ascending order
} Sequence;

extern std::vector<Sequence> sequences;

void populateSequences(void);
