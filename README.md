This fevis/tools/fuzzball subdirectory of the FEVIS repository is a
a branch of the upstream Git repository at:

https://github.com/bitblaze-fuzzball/fuzzball

It's probably best to use this directory just for changes to FuzzBALL
itself, or code that works closely enough with the existing FuzzBALL
code that it needs to be linked together.

We created this branch using the "git subtree" command which exists in
recent versions of Git. A suggested configuration is to have a remote
named fuzzball-upstream pointing at the GitHub version, which you can
create with:

git remote add fuzzball-upstream https://github.com/bitblaze-fuzzball/fuzzball.git

The command that created this subtree was:

git subtree add --prefix tools/fuzzball fuzzball-upstream master

From the web resources I was consulting, I'm guessing that the command
for merging the most recent changes from upstream into this branch
will be:

git fetch fuzzball-upstream master
git subtree pull --prefix tools/fuzzball fuzzball-upstream master

But I haven't yet tested this commands with any updates.

The rest of this file is the upstream README.md, which may still be
useful:


FuzzBALL is a symbolic execution tool for x86 (and a little ARM)
binary code, based on the BitBlaze Vine library. (The name comes from
the phrase "FUZZing Binaries with A Little Language", where "fuzzing"
is a common application of symbolic execution to bug-finding, and the
"little language" refers to the Vine intermediate language that
FuzzBALL uses for execution.  Also "fuzzball" is a common nickname for
a small kitten, and FuzzBALL was intended to be simpler and
lighter-weight than some other symbolic execution tools.)

At a high level, there are two kinds of code you can run FuzzBALL
on. First, there is any code that can execute stand-alone, without the
services of an OS or special hardware devices; this can include a
subset of code from a larger program that does need those
things. Second, there are single-threaded Linux programs, which
FuzzBALL can run by passing their system calls onto your real OS.

FuzzBALL is free software distributed under the GNU GPL: see the files
LICENSE and COPYING for details.

Compilation instructions are in the file INSTALL.

The README file includes some more detailed description of FuzzBALL
and some tutorial-style examples.

FuzzBALL's page on the Berkeley web site, at

http://bitblaze.cs.berkeley.edu/fuzzball.html

has links to some papers that build on FuzzBALL.

We are interested in your comments, questions, and feedback about
FuzzBALL via the bitblaze-users mailing list (hosted by Google Groups):

http://groups.google.com/group/bitblaze-users

