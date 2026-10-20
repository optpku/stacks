/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Proetale.WContractible
public import ReasLib.CategoryTheory.Sites.WeaklyContractible

/-!
# Weak contractibility in pro-étale sites

For affine schemes, w-contractibility of global sections is equivalent to
weak contractibility and to the finite coproduct Zariski refinement property.
These characterizations hold both in the ambient pro-étale topology and in
bounded big pro-étale sites.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace IsWContractibleRing

/-- For a commutative ring `A`, being w-contractible is equivalent to
`Spec (.of A)` being weakly contractible in the big pro-étale topology, and to
every pro-étale cover of `Spec (.of A)` admitting a finite coproduct Zariski
refinement. -/
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

namespace AlgebraicGeometry.BigProetaleSite

/-- For an affine object of a bounded big pro-étale site, w-contractibility of
its global sections, weak contractibility in the site, and the finite
coproduct Zariski refinement property of its represented scheme are equivalent. -/
@[stacks 098H]
theorem isWContractibleRing_tfae (X : BigProetaleSite.{u})
    {T : X.carrier} [IsAffine (X.toScheme.obj T)] :
    List.TFAE
      [IsWContractibleRing Γ(X.toScheme.obj T, ⊤),
        X.toGrothendieck.IsWeaklyContractible T,
        Scheme.Proetale.HasFiniteCoproductZariskiRefinement (X.toScheme.obj T)] :=
  sorry

end AlgebraicGeometry.BigProetaleSite
