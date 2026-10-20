/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Morphisms.SmoothInverseLimit
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Torsion
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Derived étale base change for a quasi-compact, quasi-separated morphism along
a nonempty directed inverse limit of smooth schemes with affine transitions is
an isomorphism on bounded-below complexes with invertible-order torsion
cohomology stalks. -/
theorem derivedBaseChange_isIso_of_smoothInverseLimit
    {I : Type u} [Preorder I] [h_nonempty : Nonempty I]
    [h_directed : IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (DS : OrderDual I ⥤ Scheme.{u})
    [h_affine : ∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    (gi : ∀ i : I, DS.obj (OrderDual.toDual i) ⟶ S)
    [h_smooth : ∀ i : I, Smooth (gi i)]
    (hgi : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DS hij ≫ gi i = gi j)
    (cS : Cone DS) (hcS : IsLimit cS) (g : cS.pt ⟶ S)
    (hg : ∀ i : I, cS.π.app (OrderDual.toDual i) ≫ gi i = g)
    {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    {X' : Scheme.{u}} (f' : X' ⟶ cS.pt) (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn.{u, u + 1} S :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E) :
    IsIso (BaseChange.derivedMapOfCommSq f g f' g' h_cart.toCommSq
      (DerivedCategory.Plus.ι.obj E)) := sorry

/-- Derived étale base change along the chosen fibre product with a nonempty
directed inverse limit of smooth schemes with affine transitions is an
isomorphism for a quasi-compact, quasi-separated morphism and bounded-below
coefficients with invertible-order torsion cohomology stalks. -/
theorem derivedBaseChange_isIso_of_smoothInverseLimit_pullback
    {I : Type u} [Preorder I] [h_nonempty : Nonempty I]
    [h_directed : IsDirected I (· ≤ ·)]
    {S : Scheme.{u}} (DS : OrderDual I ⥤ Scheme.{u})
    [h_affine : ∀ {i j : I} (hij : i ≤ j),
      IsAffineHom (OrderDualInverseSystem.transitionMap DS hij)]
    (gi : ∀ i : I, DS.obj (OrderDual.toDual i) ⟶ S)
    [h_smooth : ∀ i : I, Smooth (gi i)]
    (hgi : ∀ {i j : I} (hij : i ≤ j),
      OrderDualInverseSystem.transitionMap DS hij ≫ gi i = gi j)
    (cS : Cone DS) (hcS : IsLimit cS) (g : cS.pt ⟶ S)
    (hg : ∀ i : I, cS.π.app (OrderDual.toDual i) ≫ gi i = g)
    {X : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [HasPullback g f]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    (hE : DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn.{u, u + 1} S :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E) :
    IsIso (BaseChange.derivedMapOfCommSq f g (pullback.fst g f) (pullback.snd g f)
      (IsPullback.of_hasPullback g f).flip.toCommSq (DerivedCategory.Plus.ι.obj E)) := sorry

/-- The canonical derived comparison is an isomorphism when smooth inverse-limit,
cartesian-square, and invertible-order torsion hypotheses are supplied by `Fact`. -/
instance derivedBaseChange_isIso_of_smoothInverseLimit_of_fact
    {S T X X' : Scheme.{u}} (g : T ⟶ S)
    [h_lim : Fact (IsSmoothInverseLimit g)]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    (f' : X' ⟶ T) (g' : X' ⟶ X)
    [h_cart : Fact (IsPullback g' f' f g)]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    [hE : Fact (DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn.{u, u + 1} S :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E)] :
    IsIso (BaseChange.derivedMapOfCommSq f g f' g' h_cart.out.toCommSq
      (DerivedCategory.Plus.ι.obj E)) := by
  rcases h_lim.out with ⟨I, DS, π, hcS, gi, hn, hd, ha, hs, hgi, hg⟩
  exact derivedBaseChange_isIso_of_smoothInverseLimit
    (h_nonempty := hn) (h_directed := hd) (h_affine := ha) (h_smooth := hs)
    DS gi hgi { pt := T, π := π } hcS g hg f f' g' h_cart.out E hE.out

/-- The canonical derived comparison for the chosen fibre product is an
isomorphism when smooth inverse-limit and invertible-order torsion hypotheses
are supplied by `Fact`. -/
instance derivedBaseChange_isIso_of_smoothInverseLimit_pullback_of_fact
    {S T X : Scheme.{u}} (g : T ⟶ S)
    [h_lim : Fact (IsSmoothInverseLimit g)]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [HasPullback g f]
    (E : DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}))
    [hE : Fact (DerivedCategory.Plus.cohomologyIn
      (IsTorsionWithOrdersInvertibleOn.{u, u + 1} S :
        ObjectProperty (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) E)] :
    IsIso (BaseChange.derivedMapOfCommSq f g (pullback.fst g f) (pullback.snd g f)
      (IsPullback.of_hasPullback g f).flip.toCommSq (DerivedCategory.Plus.ι.obj E)) := by
  rcases h_lim.out with ⟨I, DS, π, hcS, gi, hn, hd, ha, hs, hgi, hg⟩
  exact derivedBaseChange_isIso_of_smoothInverseLimit_pullback
    (h_nonempty := hn) (h_directed := hd) (h_affine := ha) (h_smooth := hs)
    DS gi hgi { pt := T, π := π } hcS g hg f E hE.out

end AlgebraicGeometry.Scheme.Hom

end
