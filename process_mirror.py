import re
import urllib2
import sys

def get_all_versions(url):
    site = urllib2.urlopen(url).read()
    ans = re.findall('(sage-([0-9]*(?:\.[0-9]*)*)-Ubuntu_16.04-x86_64.tar.bz2)',site)
    all_versions = []
    for fname, ver in ans:
        if fname not in all_versions:
            all_versions.append(fname)
    return all_versions

print get_all_versions(sys.argv[1])[int(sys.argv[2])]
