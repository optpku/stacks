/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Sites.Descent.PullHom.Basic
public import ReasLib.CategoryTheory.Sites.Descent.PullHom.Computations

/-!
# Pullback of Hom morphisms in descent

Compatibility aggregate for generic algebraic and pseudofunctor-comparison computations of
`Pseudofunctor.LocallyDiscreteOpToCat.pullHom`. New consumers may import `PullHom.Basic` for
binary composition and equality elimination, or `PullHom.Computations` for iterated composites
and comparison-normalization formulas.
-/
