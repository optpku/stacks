/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.SheafPseudofunctor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsoOverOpen
public import ReasLib.CategoryTheory.Limits.CategoricalPullback.CatCommSqOver
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Small étale sheaves on proper modifications

Small étale sheaves on an algebraic space are compared with compatible sheaves on a
proper modification and a closed subspace over whose complement it is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace
open CategoricalPullback

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.EtaleSheaf

/-- The comparison functor from small étale sheaves to pairs of pullbacks with their
canonical identification on a cartesian square. -/
noncomputable def glueFunctor {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    Sheaf (smallEtaleTopology Y) (Type (u + 1)) ⥤
      CategoricalPullback (pullback j) (pullback g) :=
  CatCommSqOver.comparison
    { fst := pullback f
      snd := pullback i
      iso :=
        pullbackComp f j ≪≫
          eqToIso (congrArg (fun h ↦ pullback h) h_cart.w) ≪≫
          (pullbackComp i g).symm }

/-- The first projection of the comparison functor is pullback along the first
morphism to the base algebraic space. -/
noncomputable def glueFunctor_fst {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    glueFunctor f i j g h_cart ⋙ π₁ (pullback j) (pullback g) ≅ pullback f :=
  Iso.refl _

/-- The second projection of the comparison functor is pullback along the second
morphism to the base algebraic space. -/
noncomputable def glueFunctor_snd {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) :
    glueFunctor f i j g h_cart ⋙ π₂ (pullback j) (pullback g) ≅ pullback i :=
  Iso.refl _

/-- The structural isomorphism of the comparison functor is the composition of
pullback comparison isomorphisms transported across the cartesian square. -/
theorem glueFunctor_iso {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i)
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    ((glueFunctor f i j g h_cart).obj F).iso =
      (pullbackComp f j).app F ≪≫
        (eqToIso (congrArg (fun h ↦ pullback h) h_cart.w)).app F ≪≫
        ((pullbackComp i g).symm).app F := by
  change (pullbackComp f j ≪≫ eqToIso (congrArg (fun h ↦ pullback h) h_cart.w) ≪≫
    (pullbackComp i g).symm).app F = _
  rw [NatIso.trans_app, NatIso.trans_app]

/-- A proper morphism that is an isomorphism outside a closed subspace induces an
equivalence between small étale sheaves on the base and compatible pairs of sheaves
on its source and the closed subspace. -/
@[stacks 0GFY]
theorem glueFunctor_isEquivalence {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) [Proper f] [IsClosedImmersion i]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    (glueFunctor f i j g h_cart).IsEquivalence :=
  sorry

/-- For the chosen fibre product of a proper modification and a closed subspace,
the comparison on small étale sheaves is an equivalence when the modification is an
isomorphism over the complement. -/
theorem glueFunctor_isEquivalence_of_hasPullback
    {S : Scheme.{u}} {Y' Y Z : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) [Proper f] [IsClosedImmersion i]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    (glueFunctor f i (Limits.pullback.snd i f) (Limits.pullback.fst i f)
      (IsPullback.of_hasPullback i f).flip).IsEquivalence :=
  glueFunctor_isEquivalence f i (Limits.pullback.snd i f) (Limits.pullback.fst i f)
    (IsPullback.of_hasPullback i f).flip h_iso

/-- The comparison functor for a proper modification is canonically an equivalence
when the modification is an isomorphism over the complement of the closed subspace. -/
instance glueFunctorIsEquivalence {S : Scheme.{u}} {Y' Y Z E : AlgebraicSpace S}
    (f : Y' ⟶ Y) (i : Z ⟶ Y) (j : E ⟶ Y') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) [Proper f] [IsClosedImmersion i]
    [IsIso (openInverseImageTo f (closedImmersionComplementι i))] :
    (glueFunctor f i j g h_cart).IsEquivalence :=
  glueFunctor_isEquivalence f i j g h_cart
    (inferInstance : IsIso (openInverseImageTo f (closedImmersionComplementι i)))

end AlgebraicGeometry.AlgebraicSpace.EtaleSheaf
