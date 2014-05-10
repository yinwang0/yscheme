# YScheme - an experimental compiler for Scheme


This is the final submission for a compiler course I took from <a
href="http://en.wikipedia.org/wiki/R._Kent_Dybvig">Kent Dybvig</a> at Indiana
University. The compiler compiles a significant subset of Scheme into X64
assembly and then links it with a runtime system written in C. I made attempts
to simplify and innovate the compiler, so it is quite different from Kent's
original design.

In Kent's words, I put myself into trouble each week by doing things differently
and then get myself out of it. Sometimes I did better than his compiler,
sometimes, worse. But eventually I passed all his tests and got an A+.

A notable thing of this compiler is its use of _high-order evaluation contexts_,
an advanced technique used in <a
href="https://github.com/yinwang0/lightsabers/blob/master/cps.ss">CPS
transformers</a>, which resulted sometimes in much simpler and shorter code.


### Copyright

Copyright (c) 2008-2014 Yin Wang, All rights reserved

Only the main compiler code is here. I don't have copyright of the rest of the
code (test framework, runtime system etc)


### References

For a history of the important compiler techniques contained in this compiler,
please refer to Kent's paper:

<a href="http://www.cs.indiana.edu/~dyb/pubs/hocs.pdf">The Development of Chez
Scheme</a>


For details of the compiler framework developed for the course, please refer to

<https://github.com/akeep/nanopass-framework>
