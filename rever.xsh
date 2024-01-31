# ********************************************************************
#  This file is part of darmonpoints.
#
#        Copyright (C) 2020-2022 Julian Rüth
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
# 
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
# 
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.
# ********************************************************************

import sys

try:
  input("Are you sure you are on the main branch which is identical to origin/main? [ENTER]")
except KeyboardInterrupt:
  sys.exit(1)

from rever.activities.command import command

command('build', 'python -m build --sdist')
command('twine', 'twine upload dist/*')

$PROJECT = 'darmonpoints'

$ACTIVITIES = [
    'version_bump',
    'changelog',
    'build',
    'twine',
    'tag',
    'push_tag',
    'ghrelease',
]

$VERSION_BUMP_PATTERNS = [
  ('pyproject.toml', r"version =", 'version = "$VERSION"'),
  ('doc/conf.py', r"release =", 'release = "$VERSION"'),
]

$CHANGELOG_FILENAME = 'ChangeLog'
$CHANGELOG_TEMPLATE = 'TEMPLATE.rst'
$CHANGELOG_NEWS = 'doc/news'
$PUSH_TAG_REMOTE = 'git@github.com:mmasdeu/darmonpoints.git'

$GITHUB_ORG = 'mmasdeu'
$GITHUB_REPO = 'darmonpoints'

$GHRELEASE_ASSETS = ['dist/darmonpoints-' + $VERSION + '.tar.gz']
