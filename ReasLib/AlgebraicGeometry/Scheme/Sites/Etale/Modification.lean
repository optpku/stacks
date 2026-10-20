/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ClosedImmersion.Complement
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafPseudofunctor
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Categorical.Basic

/-!
# Small étale sheaves on proper modifications

Small étale sheaves on a scheme are compared with compatible sheaves on a proper
modification and a closed subscheme over whose complement the modification is an isomorphism.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/-- The comparison functor from small étale sheaves to pairs of pullbacks with their
canonical identification on a cartesian square. -/
noncomputable def glueFunctor {X X' Z E : Scheme.{u}} (f : X' ⟶ X) (i : Z ⟶ X)
    (j : E ⟶ X') (g : E ⟶ Z) (h_cart : IsPullback j g f i) :
    Sheaf X.smallEtaleTopology (Type (u + 1)) ⥤
      CategoricalPullback (pullback j) (pullback g) :=
  (CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
    (pullback j) (pullback g) (Sheaf X.smallEtaleTopology (Type (u + 1)))).obj
    { fst := pullback f
      snd := pullback i
      iso := pullbackComp f j ≪≫ eqToIso (congrArg pullback h_cart.w) ≪≫
        (pullbackComp i g).symm }

/-- The first projection of the comparison functor is pullback along the first
morphism to the base scheme. -/
noncomputable def glueFunctor_fst {X X' Z E : Scheme.{u}} (f : X' ⟶ X)
    (i : Z ⟶ X) (j : E ⟶ X') (g : E ⟶ Z) (h_cart : IsPullback j g f i) :
    glueFunctor f i j g h_cart ⋙ CategoricalPullback.π₁ (pullback j) (pullback g) ≅
      pullback f :=
  Iso.refl _

/-- The second projection of the comparison functor is pullback along the second
morphism to the base scheme. -/
noncomputable def glueFunctor_snd {X X' Z E : Scheme.{u}} (f : X' ⟶ X)
    (i : Z ⟶ X) (j : E ⟶ X') (g : E ⟶ Z) (h_cart : IsPullback j g f i) :
    glueFunctor f i j g h_cart ⋙ CategoricalPullback.π₂ (pullback j) (pullback g) ≅
      pullback i :=
  Iso.refl _

/-- The structural isomorphism of the comparison functor is the composition of
pullback comparison isomorphisms transported across the cartesian square. -/
theorem glueFunctor_iso {X X' Z E : Scheme.{u}} (f : X' ⟶ X) (i : Z ⟶ X)
    (j : E ⟶ X') (g : E ⟶ Z) (h_cart : IsPullback j g f i)
    (F : Sheaf X.smallEtaleTopology (Type (u + 1))) :
    ((glueFunctor f i j g h_cart).obj F).iso =
      (pullbackComp f j).app F ≪≫
        (eqToIso (congrArg pullback h_cart.w)).app F ≪≫
        ((pullbackComp i g).symm).app F := by
  change (pullbackComp f j ≪≫ eqToIso (congrArg pullback h_cart.w) ≪≫
    (pullbackComp i g).symm).app F = _
  rw [NatIso.trans_app, NatIso.trans_app]

/-- A proper morphism that is an isomorphism outside a closed subscheme induces an
equivalence between small étale sheaves on the base and compatible pairs of sheaves
on its source and the closed subscheme. -/
theorem glueFunctor_isEquivalence {X X' Z E : Scheme.{u}}
    (f : X' ⟶ X) (i : Z ⟶ X) (j : E ⟶ X') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) [IsProper f] [IsClosedImmersion i]
    (h_iso : IsIsoOverComplement f i) :
    (glueFunctor f i j g h_cart).IsEquivalence := sorry

/-- The comparison functor for a proper modification is canonically an equivalence
when its base change to the complement of the closed subscheme is an isomorphism. -/
instance glueFunctorIsEquivalence {X X' Z E : Scheme.{u}}
    (f : X' ⟶ X) (i : Z ⟶ X) (j : E ⟶ X') (g : E ⟶ Z)
    (h_cart : IsPullback j g f i) [IsProper f] [IsClosedImmersion i]
    [IsIso (Limits.pullback.snd f (closedImmersionComplement i).ι)] :
    (glueFunctor f i j g h_cart).IsEquivalence :=
  glueFunctor_isEquivalence f i j g h_cart
    (inferInstance : IsIso (Limits.pullback.snd f (closedImmersionComplement i).ι))

end AlgebraicGeometry.Scheme.EtaleSheaf
