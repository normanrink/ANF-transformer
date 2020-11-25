# ANF-transformer
Strongly-typed transformation of lambda calculus terms into A-normal form (ANF).

A simple transformation that turns general lambda calculus terms into
[A-normal form](https://en.wikipedia.org/wiki/A-normal_form)
is described in the entry
[Normal Forms](https://ucsd-progsys.github.io/liquidhaskell-blog/2016/09/01/normal-forms.lhs/)
of the
[Liquid Haskell blog](https://ucsd-progsys.github.io/liquidhaskell-blog/blog.html).
The code in this repository demonstrates how plain Haskell (with commonly used language extensions) 
can give the same correctness guarantee for the ANF transformation from
[A-normal form](https://en.wikipedia.org/wiki/A-normal_form)
as is given by the refinement types of
[Liquid Haskell](https://ucsd-progsys.github.io/liquidhaskell-blog/).

The code in this repository also extends the work in
[A-normal form](https://en.wikipedia.org/wiki/A-normal_form)
by developing a strongly-typed version of the ANF transformation
for a strongly-typed representation of lambda calculus terms.
The representation of lambda calculus terms is standard, relying
on de Bruijn-indices.
This enforces in particular that lambda calculus terms are well-scoped.
