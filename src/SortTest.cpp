/*******************************************************************************
 * src/SortTest.cpp
 *
 * Test the sorting algorithms for different small and larger inputs.
 *
 *******************************************************************************
 * Copyright (C) 2014 Timo Bingmann <tb@panthema.net>
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
 ******************************************************************************/

#include <wx/app.h>
#include <wx/stopwatch.h>
#include <wx/cmdline.h>

#include "SortArray.h"
#include "SortAlgo.h"
#include "algorithms/insertion.h"

extern std::vector<size_t> ShellSortIncrements(size_t n, ShellSortIncrementType t);

double g_delay = 0;

class SortTestApp : public wxAppConsole
{
public:
    virtual bool OnInit();
    virtual int OnRun();
    virtual void OnInitCmdLine(wxCmdLineParser& parser);
    virtual bool OnCmdLineParsed(wxCmdLineParser& parser);

private:
    wxString m_filter;
};

IMPLEMENT_APP_CONSOLE(SortTestApp);

bool SortTestApp::OnInit()
{
    if (!wxAppConsole::OnInit())
        return false;

    return true;
}

static size_t testsize[] = {
    10, 11, 12, 13, 14, 15, 16, 32,
    100, 101, 102, 103, 200,
    1024, 1337, 1627, 2048,
    3000, 4000, 7000, 9001, 10240,
    12000, 16000, 23456, 34567, 65536,
    234567, 1000000, 0
};

struct SortedCheck
{
    std::vector<ArrayItem> m_sorted;

    SortedCheck(const SortArray& sa)
        : m_sorted(sa.size())
    {
        for (size_t i = 0; i < sa.size(); ++i)
            m_sorted[i] = sa.direct(i);

        std::sort(m_sorted.begin(), m_sorted.end());
    }

    bool check(const SortArray& sa)
    {
        if (sa.size() != m_sorted.size()) return false;
        for (size_t i = 0; i < sa.size(); ++i) {
            if (m_sorted[i] != sa.direct(i))
                return false;
        }
        return true;
    }
};

int SortTestApp::OnRun()
{
    wxPrintf(_T("Sound of Sorting " PACKAGE_VERSION " - Algorithm Tester\n"));

    bool all_good = true;

    wxArrayString inputlist;
    SortArray::FillInputlist(inputlist);

    for (size_t algoi = 0; algoi < g_algolist_size; ++algoi)
    {
        const AlgoEntry& ae = g_algolist[algoi];

        if (!m_filter.IsEmpty() && !ae.name.Contains(m_filter))
            continue;

        wxPrintf(_T("-----------------------------------------------------\n"));
        wxPrintf(_T("Testing %s\n"), ae.name.c_str());

        for (size_t sizei = 0; testsize[sizei]; ++sizei)
        {
            size_t n = testsize[sizei];

            if (n > ae.max_testsize) break;

            for (size_t inputi = 0; inputi < inputlist.size(); ++inputi)
            {
                SortArray array;
                array.FillData(inputi, n);

                SortedCheck sortcheck(array);

                array.OnAlgoLaunch(ae, false);

                wxStopWatch sw;
                ae.func(array);
                long millitime = sw.Time();

                if (!array.CheckSorted()) {
                    wxPrintf(_T("FAILED(%s) "), inputlist[inputi].c_str());
                    all_good = false;
                }
                else if (!sortcheck.check(array)) {
                    wxPrintf(_T("FAILED(%s) "), inputlist[inputi].c_str());
                    all_good = false;
                }

                wxPrintf(_T("%lu/i%lu -> %lu ms. "), n, inputi, millitime);
                fflush(stdout);
            }
            wxPrintf(_T("\n"));
        }

        wxPrintf(_T("\n"));
    }

        wxPrintf(_T("\n\nShellsort gap sequences:\n"));

	uint16_t t = SHELL_1959_SHELL;
	while(1) {
		std::vector<size_t> incs = ShellSortIncrements(65536, (ShellSortIncrementType) t++);
		if(incs.size() < 2)
			break;
		for(size_t i=0; i < incs.size(); i++)
			wxPrintf("%u, ", (unsigned int) incs[i]);
		wxPrintf("...\n");
	}

    return all_good ? 0 : -1;
}

static const wxCmdLineEntryDesc g_cmdLineDesc[] =
{
#if wxCHECK_VERSION(2,9,0)
    { wxCMD_LINE_SWITCH, "h", "help",
      "displays help on the command line parameters",
      wxCMD_LINE_VAL_NONE, wxCMD_LINE_OPTION_HELP },

    { wxCMD_LINE_PARAM, NULL, NULL,
      "filter",
      wxCMD_LINE_VAL_STRING, wxCMD_LINE_PARAM_OPTIONAL },

    { wxCMD_LINE_NONE, NULL, NULL,
      NULL,
      wxCMD_LINE_VAL_NONE, wxCMD_LINE_PARAM_OPTIONAL }
#else
    { wxCMD_LINE_SWITCH, _T("h"), _T("help"),
      _T("displays help on the command line parameters"),
      wxCMD_LINE_VAL_NONE, wxCMD_LINE_OPTION_HELP },

    { wxCMD_LINE_PARAM, wxEmptyString, wxEmptyString,
      _T("filter"),
      wxCMD_LINE_VAL_STRING, wxCMD_LINE_PARAM_OPTIONAL },

    { wxCMD_LINE_NONE, wxEmptyString, wxEmptyString,
      wxEmptyString,
      wxCMD_LINE_VAL_NONE, wxCMD_LINE_PARAM_OPTIONAL }
#endif
};

void SortTestApp::OnInitCmdLine(wxCmdLineParser& parser)
{
    parser.SetDesc(g_cmdLineDesc);
    parser.SetSwitchChars(_T("-"));
}

bool SortTestApp::OnCmdLineParsed(wxCmdLineParser& parser)
{
    // to get the unnamed parameters
    for (size_t i = 0; i < parser.GetParamCount(); i++)
    {
        if (!m_filter.IsEmpty())
            m_filter.Append(_T(" "));

        m_filter.Append(parser.GetParam(i));
    }

    return true;
}
