# sat
The core problem in TCS

# Purpose
I want to learn more about SAT solving, and help others learn. I am attempting to implement a "modern" SAT
solver only by referring to blog posts and original literature. I hope that this implementation will teach
me what I want to know about SAT solvers, and I hope to share what I've learned in a series of informal blog
posts to make the next students' lives easier.

# Current Implementation
Currently it very closely follows the psuedocode as outlined in [1]. That's rather the point. I do intend to implement
additional interesting algorithms.

# Source Code Tour
The main interesting file is sat.cpp. The decision_sequence object may have some unintuitive behavior (in particular, the
fact that the "decisions" array is a permutation of all variables). Otherwise, I think the design is fairly straightforward,
if not the most straightforward.

Please also see my website, aaronandalgorithms.com, for additional commentary.

# References (not BibTeX, sorry):
1. From Total Assignment Enumeration to Modern SAT Solver, Dershowitz and Nadel, 2011, (https://arxiv.org/abs/1110.5867).
This provided the main, initial outline of the algorithm as implemented, plus was a valuable abbreviated bibliography of
what papers to take a look at next.
2. Understanding and Improving a Modern SAT Solver, Nadel's PhD Thesis, 2009, (http://www.cs.tau.ac.il/thesis/thesis/nadel.pdf).
An early chapter is a more spelled-out version of 1., except with a few subtle differences. It was a valuable counterpart
to 1., as it was those little differences that helped address some of my lingering questions.

# License
I would be happy to let anyone use this for personal-educational use without any obligation. I would be very glad to hear from
anyone whose studies I could have assisted. For any other use, feel free to email me with questions (my email is in the commits).
