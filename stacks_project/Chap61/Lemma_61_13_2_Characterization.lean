/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import ReasLib.CategoryTheory.Sites.WeaklyContractible
public import stacks_project.Chap61.Lemma_61_13_1_Refinement
public import stacks_project.Chap61.Definition_61_12_8_Presentation

/-!
# Weak contractibility of spectra of w-contractible rings

For an affine scheme `Spec (.of A)`, being a weakly contractible object of the
big pro-étale site is equivalent to `A` being w-contractible, and to every
pro-étale cover admitting a finite coproduct Zariski refinement.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v

namespace IsWContractibleRing

/-- For a commutative ring `A`, being w-contractible is equivalent to
`Spec (.of A)` being weakly contractible in the big pro-étale topology, and to
every pro-étale cover of `Spec (.of A)` admitting a finite coproduct Zariski
refinement. -/
@[stacks 098H]
theorem tfae_weaklyContractible {A : Type u} [CommRing A] :
    List.TFAE
      [IsWContractibleRing A,
        Scheme.proetaleTopology.IsWeaklyContractible (Spec (.of A)),
        Scheme.Proetale.HasFiniteCoproductZariskiRefinement (Spec (.of A))] :=
  sorry

/-- A commutative ring is w-contractible if and only if `Spec (.of A)` is
weakly contractible in the big pro-étale topology. -/
theorem iff_isWeaklyContractible {A : Type u} [CommRing A] :
    IsWContractibleRing A ↔
      Scheme.proetaleTopology.IsWeaklyContractible (Spec (.of A)) :=
  sorry

/-- An affine scheme is weakly contractible in the big pro-étale topology if
and only if its ring of global sections is w-contractible. -/
theorem iff_isWeaklyContractible_isAffine {T : Scheme.{u}} [IsAffine T] :
    IsWContractibleRing Γ(T, ⊤) ↔
      Scheme.proetaleTopology.IsWeaklyContractible T :=
  sorry

/-- The spectrum of a w-contractible ring is weakly contractible in the big
pro-étale topology. -/
instance instIsWeaklyContractible_spec {A : Type u} [CommRing A]
    [IsWContractibleRing A] :
    Scheme.proetaleTopology.IsWeaklyContractible (Spec (.of A)) :=
  sorry

end IsWContractibleRing

namespace AlgebraicGeometry.Scheme.Proetale

/-- An affine scheme is weakly contractible in the big pro-étale topology if
and only if every pro-étale cover admits a finite coproduct Zariski
refinement. -/
theorem isWeaklyContractible_iff_hasFiniteCoproductZariskiRefinement
    {T : Scheme.{u}} [IsAffine T] :
    Scheme.proetaleTopology.IsWeaklyContractible T ↔
      HasFiniteCoproductZariskiRefinement T :=
  sorry

end AlgebraicGeometry.Scheme.Proetale

namespace AlgebraicGeometry.ChosenBigProetaleSite

/-- For an affine object of a chosen big pro-étale site, w-contractibility of
global sections, weak contractibility in the chosen topology, and the finite
coproduct Zariski refinement property are equivalent. -/
theorem isWContractibleRing_tfae (X : ChosenBigProetaleSite.{u, v})
    {T : X.carrier} [IsAffine (X.toScheme.obj T)] :
    List.TFAE
      [IsWContractibleRing Γ(X.toScheme.obj T, ⊤),
        X.toGrothendieck.IsWeaklyContractible T,
        Scheme.Proetale.HasFiniteCoproductZariskiRefinement (X.toScheme.obj T)] :=
  sorry

/-- An affine object of a chosen big pro-étale site is weakly contractible if
and only if its ring of global sections is w-contractible. -/
theorem isWeaklyContractible_iff_isWContractibleRing
    (X : ChosenBigProetaleSite.{u, v}) {T : X.carrier}
    [IsAffine (X.toScheme.obj T)] :
    X.toGrothendieck.IsWeaklyContractible T ↔
      IsWContractibleRing Γ(X.toScheme.obj T, ⊤) :=
  sorry

end AlgebraicGeometry.ChosenBigProetaleSite
