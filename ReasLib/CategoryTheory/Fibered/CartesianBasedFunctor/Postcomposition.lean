/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Basic
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Postcomposition

/-!
# Postcomposition of cartesian based functors

This module restricts heterogeneous postcomposition of based functors to cartesian based
functors.  It is the right-action counterpart to `CartesianBasedFunctor.precomp` and keeps the
three total categories in independent universes.
-/

@[expose] public section

universe uC vC uS₁ vS₁ uS₂ vS₂ uS₃ vS₃ uS₄ vS₄

namespace CategoryTheory

namespace CartesianBasedFunctor

variable {C : Type uC} [Category.{vC} C]
variable {S₁ : Type uS₁} {S₂ : Type uS₂} {S₃ : Type uS₃}
variable [Category.{vS₁} S₁] [Category.{vS₂} S₂] [Category.{vS₃} S₃]
variable {p₁ : S₁ ⥤ C} {p₂ : S₂ ⥤ C} {p₃ : S₃ ⥤ C}

/-- Postcomposition by a cartesian based functor on heterogeneous cartesian Hom categories. -/
@[stacks 04W9 "cartesian postcomposition on heterogeneous Hom-categories"]
def postcomp (p₁ : S₁ ⥤ C) (G : CartesianBasedFunctor p₂ p₃) :
    CartesianBasedFunctor p₁ p₂ ⥤ CartesianBasedFunctor p₁ p₃ where
  obj F := F.comp G
  map {F H} η :=
    homMk ((BasedCategory.postcomposition
      (BasedCategory.ofFunctor p₁) G.toBasedFunctor).map η.hom)
  map_id F := by
    apply ObjectProperty.hom_ext
    apply BasedNatTrans.ext
    ext x
    exact G.toFunctor.map_id (F.toFunctor.obj x)
  map_comp η θ := by
    apply ObjectProperty.hom_ext
    apply BasedNatTrans.ext
    ext x
    exact G.toFunctor.map_comp (η.hom.toNatTrans.app x) (θ.hom.toNatTrans.app x)

/-- Cartesian postcomposition acts on objects by composition. -/
@[simp, stacks 04W9 "object readout for cartesian postcomposition"]
theorem postcomp.obj (p₁ : S₁ ⥤ C) (G : CartesianBasedFunctor p₂ p₃)
    (F : CartesianBasedFunctor p₁ p₂) :
    (postcomp p₁ G).obj F = F.comp G := rfl

/-- The based natural transformation underlying cartesian postcomposition is right whiskering. -/
@[simp, stacks 04W9 "based morphism readout for cartesian postcomposition"]
theorem postcomp.map.hom (p₁ : S₁ ⥤ C) (G : CartesianBasedFunctor p₂ p₃)
    {F H : CartesianBasedFunctor p₁ p₂} (η : F ⟶ H) :
    ((postcomp p₁ G).map η).hom =
      (BasedCategory.postcomposition
        (BasedCategory.ofFunctor p₁) G.toBasedFunctor).map η.hom := rfl

/-- The ordinary natural transformation underlying cartesian postcomposition is right
whiskering of the underlying based natural transformation. -/
@[simp, stacks 04W9 "natural-transformation readout for cartesian postcomposition"]
theorem postcomp.map.toNatTrans
    (p₁ : S₁ ⥤ C) (G : CartesianBasedFunctor p₂ p₃)
    {F H : CartesianBasedFunctor p₁ p₂} (η : F ⟶ H) :
    ((postcomp p₁ G).map η).hom.toNatTrans =
      ((BasedCategory.postcomposition
        (BasedCategory.ofFunctor p₁) G.toBasedFunctor).map η.hom).toNatTrans := rfl

/-- A component of a postcomposed cartesian transformation is obtained by applying the target
functor to the original component. -/
@[simp, stacks 04W9 "component readout for cartesian postcomposition"]
theorem postcomp.map.app
    (p₁ : S₁ ⥤ C) (G : CartesianBasedFunctor p₂ p₃)
    {F H : CartesianBasedFunctor p₁ p₂} (η : F ⟶ H) (x : S₁) :
    ((postcomp p₁ G).map η).hom.toNatTrans.app x =
      G.toFunctor.map (η.hom.toNatTrans.app x) := rfl

/-- Postcomposition by the identity cartesian based functor is the identity Hom functor. -/
@[simp, stacks 04W9 "identity law for cartesian postcomposition"]
theorem postcomp.id (p₁ : S₁ ⥤ C) (p₂ : S₂ ⥤ C) :
    postcomp p₁ (CartesianBasedFunctor.id p₂) =
      𝟭 (CartesianBasedFunctor p₁ p₂) := rfl

/-- Postcomposition by a composite is the composite of the two postcomposition functors. -/
@[stacks 04W9 "composition law for cartesian postcomposition"]
theorem postcomp.comp
    {S₄ : Type uS₄} [Category.{vS₄} S₄]
    (p₁ : S₁ ⥤ C) {p₄ : S₄ ⥤ C}
    (F : CartesianBasedFunctor p₂ p₃) (G : CartesianBasedFunctor p₃ p₄) :
    postcomp p₁ (F.comp G) = postcomp p₁ F ⋙ postcomp p₁ G := rfl

/-- Postcomposition by an equivalence over the base is an equivalence of heterogeneous cartesian
Hom categories. -/
@[stacks 04W9 "equivalence transport along cartesian postcomposition"]
instance postcomp.isEquivalence
    (p₁ : S₁ ⥤ C) (G : CartesianBasedFunctor p₂ p₃)
    [hG : G.toBasedFunctor.IsEquivalence] :
    (postcomp p₁ G).IsEquivalence := by
  rcases hG.nonempty with ⟨e⟩
  letI : e.inverse.IsEquivalence := ⟨⟨e.symm⟩⟩
  let G' : CartesianBasedFunctor p₃ p₂ := ofIsEquivalence e.inverse
  refine Functor.IsEquivalence.mk' (postcomp p₁ G')
    (NatIso.ofComponents (fun F => ObjectProperty.isoMk _
      (BasedNatIso.mkNatIso
        (Functor.isoWhiskerLeft F.toFunctor
          ((BasedNatTrans.forgetful _ _).mapIso e.unitIso))
        (BasedCategory.whiskerLeft F.toBasedFunctor e.unitIso.hom).isHomLift'))
      ?_)
    (NatIso.ofComponents (fun F => ObjectProperty.isoMk _
      (BasedNatIso.mkNatIso
        (Functor.isoWhiskerLeft F.toFunctor
          ((BasedNatTrans.forgetful _ _).mapIso e.counitIso))
        (BasedCategory.whiskerLeft F.toBasedFunctor e.counitIso.hom).isHomLift'))
      ?_)
  · intro F H η
    apply ObjectProperty.hom_ext
    apply BasedNatTrans.ext
    ext x
    exact e.unitIso.hom.toNatTrans.naturality (η.hom.toNatTrans.app x)
  · intro F H η
    apply ObjectProperty.hom_ext
    apply BasedNatTrans.ext
    ext x
    exact e.counitIso.hom.toNatTrans.naturality (η.hom.toNatTrans.app x)

/- Axiom audit: the object and morphism actions retain supplied cartesian functor and vertical
transformation data. The equivalence proof uses quasi-inverse data supplied by `hG`; its inverse
preserves strongly cartesian arrows by the existing equivalence-transport theorem. -/

end CartesianBasedFunctor

end CategoryTheory
