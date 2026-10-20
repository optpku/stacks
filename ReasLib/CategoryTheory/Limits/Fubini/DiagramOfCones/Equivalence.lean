/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Limits.Fubini.DiagramOfCones.Totalization

/-!
# Cone Fubini equivalence

When every row cone is limiting, cone totalization and the row-point
construction form an equivalence of cone categories.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Limits

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory Functor

variable {I : Type u₁} [Category.{v₁} I]
variable {J : Type u₂} [Category.{v₂} J]
variable {C : Type u₃} [Category.{v₃} C]

namespace DiagramOfCones

variable {F : I ⥤ J ⥤ C} (D : DiagramOfCones F)

section

namespace Implementation

/-- Compatibility of the identity vertex isomorphism with the legs of an outer cone. -/
private theorem conePointsTotalIso_hom_app (hD : ∀ i, IsLimit (D.obj i))
    (c : Cone D.conePoints) (i : I) :
    c.π.app i =
      (Iso.refl c.pt).hom ≫
        ((D.totalConeFunctor ⋙ D.conePointsFunctor hD).obj c).π.app i := sorry
/- Proof strategy: use `IsLimit.hom_ext (hD i)` and reduce both sides after
postcomposition with every row projection. -/

/-- Component of the unit isomorphism for cone totalization. -/
private def conePointsTotalIso (hD : ∀ i, IsLimit (D.obj i))
    (c : Cone D.conePoints) :
    c ≅ (D.totalConeFunctor ⋙ D.conePointsFunctor hD).obj c :=
  Cone.ext (Iso.refl c.pt) (conePointsTotalIso_hom_app D hD c)

/-- Naturality of the unit isomorphism for cone totalization. -/
private theorem conePointsTotalIso_naturality (hD : ∀ i, IsLimit (D.obj i))
    {c₁ c₂ : Cone D.conePoints} (α : c₁ ⟶ c₂) :
    α ≫ (conePointsTotalIso D hD c₂).hom =
      (conePointsTotalIso D hD c₁).hom ≫
        (D.totalConeFunctor ⋙ D.conePointsFunctor hD).map α := sorry
/- Proof strategy: apply cone-morphism extensionality; all component isomorphisms have identity
vertex maps. -/

/-- Unit natural isomorphism for cone totalization. -/
private def conePointsTotalNatIso (hD : ∀ i, IsLimit (D.obj i)) :
    𝟭 (Cone D.conePoints) ≅ D.totalConeFunctor ⋙ D.conePointsFunctor hD :=
  NatIso.ofComponents (conePointsTotalIso D hD)
    (conePointsTotalIso_naturality D hD)

/-- Compatibility of the identity vertex isomorphism with the legs of a total cone. -/
private theorem totalConePointsIso_hom_app (hD : ∀ i, IsLimit (D.obj i))
    (c : Cone (uncurry.obj F)) (p : I × J) :
    ((D.conePointsFunctor hD ⋙ D.totalConeFunctor).obj c).π.app p =
      (Iso.refl c.pt).hom ≫ c.π.app p := sorry
/- Proof strategy: unfold the totalized projection and use the defining factorization through the
limiting row cone. -/

/-- Component of the counit isomorphism for cone totalization. -/
private def totalConePointsIso (hD : ∀ i, IsLimit (D.obj i))
    (c : Cone (uncurry.obj F)) :
    (D.conePointsFunctor hD ⋙ D.totalConeFunctor).obj c ≅ c :=
  Cone.ext (Iso.refl c.pt) (totalConePointsIso_hom_app D hD c)

/-- Naturality of the counit isomorphism for cone totalization. -/
private theorem totalConePointsIso_naturality (hD : ∀ i, IsLimit (D.obj i))
    {c₁ c₂ : Cone (uncurry.obj F)} (α : c₁ ⟶ c₂) :
    (D.conePointsFunctor hD ⋙ D.totalConeFunctor).map α ≫
        (totalConePointsIso D hD c₂).hom =
      (totalConePointsIso D hD c₁).hom ≫ α := sorry
/- Proof strategy: apply cone-morphism extensionality; all component isomorphisms have identity
vertex maps. -/

/-- Counit natural isomorphism for cone totalization. -/
private def totalConePointsNatIso (hD : ∀ i, IsLimit (D.obj i)) :
    D.conePointsFunctor hD ⋙ D.totalConeFunctor ≅ 𝟭 (Cone (uncurry.obj F)) :=
  NatIso.ofComponents (totalConePointsIso D hD)
    (totalConePointsIso_naturality D hD)

/-- The chosen unit and counit satisfy the equivalence triangle identity. -/
private theorem coneEquivalence_triangle (hD : ∀ i, IsLimit (D.obj i))
    (c : Cone D.conePoints) :
    D.totalConeFunctor.map ((conePointsTotalNatIso D hD).hom.app c) ≫
        (totalConePointsNatIso D hD).hom.app (D.totalConeFunctor.obj c) =
      𝟙 (D.totalConeFunctor.obj c) := sorry
/- Proof strategy: apply cone-morphism extensionality; every vertex map reduces to an identity. -/

end Implementation

/-- Limiting row cones identify outer cones on their vertices with cones on the uncurried
diagram. -/
def coneEquivalence (hD : ∀ i, IsLimit (D.obj i)) :
    Cone D.conePoints ≌ Cone (uncurry.obj F) where
  functor := D.totalConeFunctor
  inverse := D.conePointsFunctor hD
  unitIso := Implementation.conePointsTotalNatIso D hD
  counitIso := Implementation.totalConePointsNatIso D hD
  functor_unitIso_comp := Implementation.coneEquivalence_triangle D hD

/-- The forward functor of the cone equivalence is totalization. -/
@[simp]
lemma coneEquivalence_functor (hD : ∀ i, IsLimit (D.obj i)) :
    (D.coneEquivalence hD).functor = D.totalConeFunctor := sorry
/- Proof strategy: unfold `coneEquivalence`; its forward-functor field is definitionally
`D.totalConeFunctor`. -/

/-- The inverse functor of the cone equivalence is the row-point functor. -/
@[simp]
lemma coneEquivalence_inverse (hD : ∀ i, IsLimit (D.obj i)) :
    (D.coneEquivalence hD).inverse = D.conePointsFunctor hD := sorry
/- Proof strategy: unfold `coneEquivalence`; its inverse field is definitionally
`D.conePointsFunctor hD`. -/

end

end DiagramOfCones

end CategoryTheory.Limits
