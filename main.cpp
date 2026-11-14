#include <iostream>
#include <fstream>
#include <string>
#include <cstdint>
#include <cstdlib>
#include <cstring>
#include <vector>
#include <algorithm>
#include <random>
#include <chrono>

using namespace std;

typedef uint64_t u64;

const int INF = 1000000000;
const u64 M1 = 1000000007ULL, B1 = 911382323ULL;
const u64 M2 = 998244353ULL,  B2 = 972663749ULL;
const int SIGMA = 5;

const string LETTER = "$ACGT";

static int code(char c) {
    switch (c) {
        case '$': return 0;
        case 'A': return 1;
        case 'C': return 2;
        case 'G': return 3;
        case 'T': return 4;
        default:  return -1;
    }
}

static int castom_dist(const char *a, long n, const char *b, long m, long k) {
    if (labs(n - m) > k)
        return INF;
    const long w = 2 * k + 1;
    vector<int> buf1(w, INF), buf2(w, INF);
    int *prev = buf1.data(), *now = buf2.data();

    for (long j = 0; j <= min(n, k); j++)
        prev[j + k] = (int)j;

    for (long i = 1; i <= m; i++) {
        const char bi = b[i - 1];
        long j = max(0L, i - k);
        const long right_now = min(n, i + k);
        long idx = j - i + k;
        int left;

        if (j == 0) {
            now[idx] = left = (int)i;
            j++, idx++;
        } else {
            int best = prev[0] + (a[j - 1] != bi);
            int del = prev[1] + 1;
            if (del < best) best = del;
            now[0] = left = best;
            j++, idx++;
        }

        const long last = (right_now - i + k == w - 1) ? right_now - 1 : right_now;

        const char *pa = a + (j - 1);
        const int *pp = prev + idx;
        int *pn = now + idx;
        for (long cnt = last - j + 1; cnt > 0; cnt--) {
            int best = *pp + (*pa != bi);
            int del = pp[1] + 1;
            int ins = left + 1;
            best = best < del ? best : del;
            best = best < ins ? best : ins;
            *pn = left = best;
            pa++, pp++, pn++;
        }
        j = last + 1;

        if (j <= right_now) {
            int best = prev[w - 1] + (a[j - 1] != bi);
            int ins = left + 1;
            now[w - 1] = best < ins ? best : ins;
        }
        swap(prev, now);
    }

    return prev[n - m + k];
}

static int edit_distance(const string &a, const string &b, long k = 100) {
    int res = castom_dist(a.data(), a.size(), b.data(), b.size(), k);
    while (res > k) {
        k *= 2;
        res = castom_dist(a.data(), a.size(), b.data(), b.size(), k);
    }
    return res;
}

static u64 power(u64 b, long e, u64 mod) {
    u64 r = 1;
    b %= mod;
    while (e > 0) {
        if (e & 1) r = r * b % mod;
        b = b * b % mod;
        e >>= 1;
    }
    return r;
}

static vector<u64> kmer_codes(const string &st, long k) {
    long n = st.size();
    vector<u64> codes;
    codes.reserve(n - k + 1);
    if (k <= 31) {
        u64 mask = (1ULL << (2 * k)) - 1;
        u64 code_ = 0;
        for (long i = 0; i < k - 1; i++)
            code_ = (code_ << 2) | (u64)(code(st[i]) - 1);
        for (long i = k - 1; i < n; i++) {
            code_ = ((code_ << 2) | (u64)(code(st[i]) - 1)) & mask;
            codes.push_back(code_);
        }
    } else {
        u64 p1 = power(B1, k, M1);
        u64 p2 = power(B2, k, M2);
        u64 h1 = 0, h2 = 0;
        for (long i = 0; i < k; i++) {
            u64 v = code(st[i]);
            h1 = (h1 * B1 + v) % M1;
            h2 = (h2 * B2 + v) % M2;
        }
        codes.push_back(h1 * M2 + h2);
        for (long i = k; i < n; i++) {
            u64 v = code(st[i]), o = code(st[i - k]);
            h1 = (h1 * B1 + v + M1 * M1 - o * p1) % M1;
            h2 = (h2 * B2 + v + M2 * M2 - o * p2) % M2;
            codes.push_back(h1 * M2 + h2);
        }
    }
    return codes;
}

static string mostFrequentKMer(const string &st, long k) {
    vector<u64> codes = kmer_codes(st, k);
    vector<u64> all(codes);
    sort(all.begin(), all.end());

    vector<u64> kmers;
    vector<int> counts;
    for (size_t i = 0; i < all.size(); i++) {
        if (!kmers.empty() && kmers.back() == all[i]) {
            counts.back() += 1;
        } else {
            kmers.push_back(all[i]);
            counts.push_back(1);
        }
    }

    size_t best = 0;
    for (size_t t = 1; t < counts.size(); t++)
        if (counts[t] > counts[best])
            best = t;

    size_t i = find(codes.begin(), codes.end(), kmers[best]) - codes.begin();
    return st.substr(i, k);
}

static vector<int> encode(const string &st) {
    vector<int> s(st.size() + 1, 0);
    for (size_t i = 0; i < st.size(); i++)
        s[i] = code(st[i]);
    return s;
}

static vector<int> suffix_array(const vector<int> &s) {
    int n = s.size();
    vector<int> sa(n), rank(s), tmp(n), new_rank(n);
    vector<int> cnt(max(n, SIGMA) + 1);

    for (int i = 0; i < n; i++) cnt[s[i] + 1]++;
    for (int c = 1; c < (int)cnt.size(); c++) cnt[c] += cnt[c - 1];
    for (int i = 0; i < n; i++) sa[cnt[s[i]]++] = i;

    for (int k = 1;; k *= 2) {
        if (k > 1) {
            new_rank[sa[0]] = 0;
            for (int j = 1; j < n; j++) {
                int prev = sa[j - 1], cur = sa[j];
                bool differ = rank[prev] != rank[cur] ||
                              rank[(prev + k / 2) % n] != rank[(cur + k / 2) % n];
                new_rank[cur] = new_rank[prev] + differ;
            }
            rank.swap(new_rank);
            if (rank[sa[n - 1]] == n - 1)
                return sa;
        }

        for (int j = 0; j < n; j++)
            tmp[j] = ((sa[j] - k) % n + n) % n;

        fill(cnt.begin(), cnt.end(), 0);
        for (int j = 0; j < n; j++) cnt[rank[tmp[j]] + 1]++;
        for (int c = 1; c < (int)cnt.size(); c++) cnt[c] += cnt[c - 1];
        for (int j = 0; j < n; j++) sa[cnt[rank[tmp[j]]]++] = tmp[j];
    }
}

static string inverse_bwt(string st) {
    int n = st.size();

    for (int i = 0; i < n; i++)
        st[i] = code(st[i]);

    vector<int> rank(n);
    int total_shift[5] = {0, 0, 0, 0, 0};
    for (int i = 0; i < n; i++)
        rank[i] = total_shift[(int)st[i]]++;

    int before = 0;
    for (int c = 0; c < 5; c++) {
        int count = total_shift[c];
        total_shift[c] = before;
        before += count;
    }

    string fin(n - 1, '?');
    int row = 0;
    for (int pos = n - 2; pos >= 0; pos--) {
        int cur = st[row];
        fin[pos] = LETTER[cur];
        row = total_shift[cur] + rank[row];
    }
    return fin;
}

static vector<int> build_bwt(const vector<int> &s, const vector<int> &sa) {
    int n = s.size();
    vector<int> bwt(n);
    for (int j = 0; j < n; j++)
        bwt[j] = s[(sa[j] - 1 + n) % n];
    return bwt;
}

static vector<int> build_total_shift(const vector<int> &s) {
    vector<int> counts(SIGMA, 0), total_shift(SIGMA, 0);
    for (int c : s)
        counts[c]++;
    for (int c = 1; c < SIGMA; c++)
        total_shift[c] = total_shift[c - 1] + counts[c - 1];
    return total_shift;
}

static vector<vector<int>> build_occ(const vector<int> &bwt) {
    int n = bwt.size();
    vector<vector<int>> occ(SIGMA, vector<int>(n + 1, 0));
    for (int c = 0; c < SIGMA; c++) {
        vector<int> &row = occ[c];
        for (int j = 0; j < n; j++)
            row[j + 1] = row[j] + (bwt[j] == c);
    }
    return occ;
}

static pair<int, int> fm_find(const string &read, const vector<int> &total_shift,
                              const vector<vector<int>> &occ) {
    int lo = 0, hi = (int)occ[0].size() - 1;
    for (int i = (int)read.size() - 1; i >= 0; i--) {
        int c = code(read[i]);
        if (c <= 0)
            return {0, 0};
        lo = total_shift[c] + occ[c][lo];
        hi = total_shift[c] + occ[c][hi];
        if (lo >= hi)
            return {0, 0};
    }
    return {lo, hi};
}

static int covered_bases(const string &genome, const vector<string> &reads) {
    vector<int> s = encode(genome);
    vector<int> sa = suffix_array(s);
    vector<int> total_shift = build_total_shift(s);
    vector<vector<int>> occ = build_occ(build_bwt(s, sa));

    int g = genome.size();
    vector<int> diff(g + 1, 0);
    for (const string &read : reads) {
        pair<int, int> r = fm_find(read, total_shift, occ);
        if (r.second - r.first == 1) {
            int p = sa[r.first];
            diff[p] += 1;
            diff[p + read.size()] -= 1;
        }
    }

    int covered = 0, cover = 0;
    for (int i = 0; i < g; i++) {
        cover += diff[i];
        if (cover > 0)
            covered++;
    }
    return covered;
}

static string read_fasta(const string &path) {
    ifstream in(path);
    if (!in) {
        cerr << "cannot open " << path << "\n";
        exit(2);
    }
    string genome, line;
    while (getline(in, line)) {
        if (line.empty() || line[0] == '>')
            continue;
        for (char c : line)
            if (!isspace((unsigned char)c))
                genome += (char)toupper((unsigned char)c);
    }
    return genome;
}

int main(int argc, char **argv) {
	if (argc < 3) {
		cerr << "Usage: " << argv[0] << " <genome.fasta> <reads.fastq>\n";
		return 1;
	}

	string genome = read_fasta(argv[1]);
	vector<string> reads;
	ifstream in(argv[2]);
	if (!in) {
		cerr << "cannot open " << argv[2] << "\n";
		return 2;
	}
	string header, seq, plus, qual;
	while (getline(in, header)) {
		if (header.empty())
			continue;
		if (header[0] != '@' || !getline(in, seq) || !getline(in, plus) ||
		    !getline(in, qual) || plus.empty() || plus[0] != '+') {
			cerr << "bad FASTQ record after read " << reads.size() << "\n";
			return 3;
		}
		if (!seq.empty() && seq.back() == '\r')
			seq.pop_back();
		reads.push_back(seq);
	}
	cerr << "reads: " << reads.size() << "\n";

	int covered = covered_bases(genome, reads);
	cout << "Covered bases: " << covered << "\n";
	return 0;
}