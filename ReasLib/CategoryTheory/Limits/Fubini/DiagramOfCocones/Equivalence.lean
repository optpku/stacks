/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Limits.Fubini.DiagramOfCocones.Totalization

/-!
# Cocone Fubini equivalence

When every row cocone is colimiting, cocone totalization and the row-point
construction form an equivalence of cocone categories.
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

namespace DiagramOfCocones

variable {F : I ⥤ J ⥤ C} (D : DiagramOfCocones F)

section

namespace Implementation

/-- Compatibility of the identity vertex isomorphism with the legs of an outer cocone. -/
private theorem coconePointsTotalIso_hom_app (hD : ∀ i, IsColimit (D.obj i))
    (c : Cocone D.coconePoints) (i : I) :
    c.ι.app i ≫ (Iso.refl c.pt).hom =
      ((D.totalCoconeFunctor ⋙ D.coconePointsFunctor hD).obj c).ι.app i := sorry
/- Proof strategy: use `IsColimit.hom_ext (hD i)`; after precomposition with every row leg the
claim is `α.w`. -/

/-- Component of the unit isomorphism for cocone totalization. -/
private def coconePointsTotalIso (hD : ∀ i, IsColimit (D.obj i))
    (c : Cocone D.coconePoints) :
    c ≅ (D.totalCoconeFunctor ⋙ D.coconePointsFunctor hD).obj c :=
  Cocone.ext (Iso.refl c.pt) (coconePointsTotalIso_hom_app D hD c)

/-- Naturality of the unit isomorphism for cocone totalization. -/
private theorem coconePointsTotalIso_naturality (hD : ∀ i, IsColimit (D.obj i))
    {c₁ c₂ : Cocone D.coconePoints} (α : c₁ ⟶ c₂) :
    α ≫ (coconePointsTotalIso D hD c₂).hom =
      (coconePointsTotalIso D hD c₁).hom ≫
        (D.totalCoconeFunctor ⋙ D.coconePointsFunctor hD).map α := sorry
/- Proof strategy: apply cocone-morphism extensionality; all component isomorphisms have identity
vertex maps. -/

/-- Unit natural isomorphism for cocone totalization. -/
private def coconePointsTotalNatIso (hD : ∀ i, IsColimit (D.obj i)) :
    𝟭 (Cocone D.coconePoints) ≅ D.totalCoconeFunctor ⋙ D.coconePointsFunctor hD :=
  NatIso.ofComponents (coconePointsTotalIso D hD)
    (coconePointsTotalIso_naturality D hD)

/-- Compatibility of the identity vertex isomorphism with the legs of a total cocone. -/
private theorem totalCoconePointsIso_hom_app (hD : ∀ i, IsColimit (D.obj i))
    (c : Cocone (uncurry.obj F)) (p : I × J) :
    ((D.coconePointsFunctor hD ⋙ D.totalCoconeFunctor).obj c).ι.app p ≫
        (Iso.refl c.pt).hom =
      c.ι.app p := sorry
/- Proof strategy: unfold the totalized leg and use the defining factorization through the
colimiting row cocone. -/

/-- Component of the counit isomorphism for cocone totalization. -/
private def totalCoconePointsIso (hD : ∀ i, IsColimit (D.obj i))
    (c : Cocone (uncurry.obj F)) :
    (D.coconePointsFunctor hD ⋙ D.totalCoconeFunctor).obj c ≅ c :=
  Cocone.ext (Iso.refl c.pt) (totalCoconePointsIso_hom_app D hD c)

/-- Naturality of the counit isomorphism for cocone totalization. -/
private theorem totalCoconePointsIso_naturality (hD : ∀ i, IsColimit (D.obj i))
    {c₁ c₂ : Cocone (uncurry.obj F)} (α : c₁ ⟶ c₂) :
    (D.coconePointsFunctor hD ⋙ D.totalCoconeFunctor).map α ≫
        (totalCoconePointsIso D hD c₂).hom =
      (totalCoconePointsIso D hD c₁).hom ≫ α := sorry
/- Proof strategy: apply cocone-morphism extensionality; all component isomorphisms have identity
vertex maps. -/

/-- Counit natural isomorphism for cocone totalization. -/
private def totalCoconePointsNatIso (hD : ∀ i, IsColimit (D.obj i)) :
    D.coconePointsFunctor hD ⋙ D.totalCoconeFunctor ≅ 𝟭 (Cocone (uncurry.obj F)) :=
  NatIso.ofComponents (totalCoconePointsIso D hD)
    (totalCoconePointsIso_naturality D hD)

/-- The chosen unit and counit satisfy the equivalence triangle identity. -/
private theorem coconeEquivalence_triangle (hD : ∀ i, IsColimit (D.obj i))
    (c : Cocone D.coconePoints) :
    D.totalCoconeFunctor.map ((coconePointsTotalNatIso D hD).hom.app c) ≫
        (totalCoconePointsNatIso D hD).hom.app (D.totalCoconeFunctor.obj c) =
      𝟙 (D.totalCoconeFunctor.obj c) := sorry
/- Proof strategy: apply cocone-morphism extensionality; every vertex map reduces to an identity. -/

end Implementation

/-- Colimiting row cocones identify outer cocones on their vertices with cocones on the
uncurried diagram. -/
def coconeEquivalence (hD : ∀ i, IsColimit (D.obj i)) :
    Cocone D.coconePoints ≌ Cocone (uncurry.obj F) where
  functor := D.totalCoconeFunctor
  inverse := D.coconePointsFunctor hD
  unitIso := Implementation.coconePointsTotalNatIso D hD
  counitIso := Implementation.totalCoconePointsNatIso D hD
  functor_unitIso_comp := Implementation.coconeEquivalence_triangle D hD

/-- The forward functor of the cocone equivalence is totalization. -/
@[simp]
lemma coconeEquivalence_functor (hD : ∀ i, IsColimit (D.obj i)) :
    (D.coconeEquivalence hD).functor = D.totalCoconeFunctor := sorry
/- Proof strategy: unfold `coconeEquivalence`; its forward-functor field is definitionally
`D.totalCoconeFunctor`. -/

/-- The inverse functor of the cocone equivalence is the row-point functor. -/
@[simp]
lemma coconeEquivalence_inverse (hD : ∀ i, IsColimit (D.obj i)) :
    (D.coconeEquivalence hD).inverse = D.coconePointsFunctor hD := sorry
/- Proof strategy: unfold `coconeEquivalence`; its inverse field is definitionally
`D.coconePointsFunctor hD`. -/

end

end DiagramOfCocones

end CategoryTheory.Limits
