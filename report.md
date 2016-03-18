# Introduction

Context-free grammars (CFGs) are a common way of specifying formal languages, including for example the syntax of programming languages (from K&R C to modern ECMAScript). They provide a natural, compact representation of structured data. There are a number of parser-generators which accept CFGs (often with some restrictions), in Haskell and other languages, but another application is often overlooked: namely, generating strings matching the grammar. This library provides that capability in Haskell, based on a paper[1] by Bruce McKenzie.


# What is provided

At the moment, this library provides functions which:

- Given a grammar of appropriate form, the tables mentioned above, and a random generator, produce a random string of the desired length
-- This method augments the tables, if necessary, and returns them
- Identify any nonterminals which can derive the empty string
- Eliminate the same
- Identify any nonterminals which can derive themselves
- Eliminate all unit productions, i.e., those of the form (A => B, with no additional symbols)
- Given an arbitrary grammar and a string, produce all potentially infinitely many parses of that string using that grammar
- Reduce a parse tree


# Approach

Mathematically speaking, a parser is sufficient to provide a generator: generate string at random and discard those rejected by the parser. Obviously this approach is generally undesirable on time complexity considerations, especially for grammars whose languages are sparse. A slightly more sophisticated approach to the problem exploits the nature of CFGs: given a string of terminal and nonterminal symbols, replace a random nonterminal with one of its productions. Unfortunately, this process is not guaranteed to terminate: applying this to the language S->SS|a only terminates approximately 87% of the time. With sufficient analysis of the grammar this can be avoided (for example, branch-and-bound methods can guide production towards strings of a desired length for non-pathological grammars), but this is difficult to implement correctly and necessarily weights strings differently depending on the grammar, even between two grammars which represent the same language. Other techniques require the grammar to be in a normal form.

The technique used here imposes minimal requirements on the structure of the grammar: specifically, no nonterminal symbol may produce the empty string, and no nonterminal may produce itself via any series of productions. This library provides helper methods to transform an arbitrary grammar into an equivalent one meeting these requirements. Given such a grammar and a desired length of generated string n, the algorithm used here builds a table describing how many strings of length 1 through n each nonterminal and suffix of each production can produce. This requires O(n^2) time and space, according to the paper, although I believe the requirement is actually O(n^3) space if all strings are to be weighted precisely equally. (Specifically, it requires n^2 counts, but the counts are potentially exponential in *n*, so each requires O(n) space to store precisely.) Once these tables have been produced, a random string of any length ≤ n can be generated in linear time, which is obviously the fastest theoretically possible.


# Implementation miscellania

The algorithm given in [1] is described using imperative iterative language, right down to K&R C-style comments, and contains a handful of minor errors. The first task was to adapt it to a functional style. Because a core aspect of the algorithm is, essentially, memoization, some state management is unavoidable; it is internally handled here by the `State` monad, where possible. Rather than relying on a particular ordering for the productions in the grammar, `Map` of the appropriate type are created and passed around.

Some of the functions require grammars of particular forms. Because it is not (as far as I am aware) possible to put restrictions on Haskell types of the form "does not contain any unit productions or nullable symbols", we instead only construct those types inside of functions which provide the appropriate guarantees, and do not export the constructors for those types. This provides the best practical guarantee of type-safety we can arrange.

The parser is a very straightforward implementation of Earley's algorithm, adapted slightly to support arbitrary grammars (i.e. including those with nonterminals which produce the empty string). It is not particularly clever or performant, but it makes up for this in generality and simplicity: without explicit type annotations it is a bare 30 lines, and the parse-tree reducer is one.


# Future work

One of the major applications of this library is generative testing: Haskell's ecosystem in particular has a strong culture of generative testing, particularly via QuickCheck. This relies on the ability to create structured data of appropriate form. It's possible to do this with QuickCheck already, but somewhat laborious; in a number of cases, simply specifying a grammar for the data would be substantially easier. To that end, this library should eventually provide an interface for QuickCheck.

Dovetailing into the above, there is no particular reason except historical accident that the generator and parser should respectively produce and consume strings (which is to say, lists of characters) as opposed to lists of arbitrary values. Parsers already frequently operate on token streams produced by a tokenizer as opposed to raw strings. It would be straightforward, and valuable, to modify the library to work on `Eq a => [a]`s instead of `[Char]`s: for the particular case of generating and consuming token streams (particularly valuable for the generator, which requires time proportional to the length of the input list, where presumably a stream of tokens would be much shorter than a stream of characters), and for other unforseen applications.


# References

McKenzie, Bruce. Generating Strings at Random from a Context Free Grammar. 1997.