/* tempdir.hpp — a self-cleaning temporary directory for the storage/durability
 * tests (storage, hardening, resilience), which each had their own near-
 * identical copy. POSIX-only; these suites are native-only anyway. */
#ifndef SYNC_TEST_TEMPDIR_HPP
#define SYNC_TEST_TEMPDIR_HPP

#include <dirent.h>
#include <unistd.h>

#include <cstdio>
#include <cstdlib>
#include <string>
#include <vector>

namespace synctest {

struct TempDir {
    std::string path;

    explicit TempDir(const char *prefix = "sync_test") {
        std::string tmpl = "/tmp/" + std::string(prefix) + "_XXXXXX";
        std::vector<char> buf(tmpl.begin(), tmpl.end());
        buf.push_back('\0');
        const char *p = mkdtemp(buf.data());
        if (p) path = p;
    }

    ~TempDir() {
        if (path.empty()) return;
        if (DIR *d = opendir(path.c_str())) {
            while (struct dirent *e = readdir(d)) {
                std::string n = e->d_name;
                if (n != "." && n != "..")
                    std::remove((path + "/" + n).c_str());
            }
            closedir(d);
        }
        rmdir(path.c_str());
    }

    /* Path to a named file inside the directory. */
    std::string file(const std::string &n) const { return path + "/" + n; }
};

} // namespace synctest

#endif /* SYNC_TEST_TEMPDIR_HPP */
