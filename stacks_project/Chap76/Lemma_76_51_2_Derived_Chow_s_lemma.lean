/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap76.Lemma_76_51_2_Derived_Chow_s_lemma_Presentation

/-!
# Derived Chow's lemma for algebraic spaces

A separated algebraic space of finite presentation over a ring admits a derived
Chow presentation at every point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedChowPresentation

/-- Lemma 76.51.2 (Derived Chow's lemma). Let `A` be a ring and let `X` be a
separated algebraic space of finite presentation over `A`. For every point
`x` of `Points X` there exist `n : ℕ`, a closed subspace `Z` of
`ProjectiveSpace n X`, a point `z` of `Points Z.X`, an open `V` of
`ofScheme n (Spec (CommRingCat.of A))`, and `E` in
`ModuleDerived (ProjectiveSpace n X)` such that `Z.ι` is of finite presentation,
`c : Z ⟶ ℙⁿ_A` is a closed immersion over `V`, the restriction of `b : Z ⟶ X` to
`W = c⁻¹(V)` is étale, `z` lies in `W` with `b(z) = x`,
`E` restricted to `X ×_A V` is isomorphic to `(b, c)_* 𝒪_Z` restricted to
`X ×_A V`, and `E` is pseudo-coherent and supported on `Z`. -/
@[stacks 0CTR]
theorem exists_of_separated_finitePresentation {A : Type u} [CommRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Separated (toBase X)]
    [FinitePresentation (toBase X)] (x : Points X) :
    Nonempty (DerivedChowPresentation x) := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedChowPresentation
