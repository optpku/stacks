module

public import ReasLib.CategoryTheory.Limits.CategoricalPullback.Map
public import ReasLib.CategoryTheory.Functor.Equivalence

/-!
# Quasi-inverses of categorical cospan transformations

Explicit cospan-level inverse data and its induced quasi-inverse and equivalence APIs for maps of
categorical pullbacks.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Limits.CategoricalPullback
open scoped CategoricalPullback

namespace CategoryTheory
namespace Limits.CatCospanTransform

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {X : Type u₁} [Category.{v₁} X]
variable {Y : Type u₂} [Category.{v₂} Y]
variable {Z : Type u₃} [Category.{v₃} Z]
variable {A : Type u₄} [Category.{v₄} A]
variable {B : Type u₅} [Category.{v₅} B]
variable {C : Type u₆} [Category.{v₆} C]
variable {H : X ⥤ Z} {I : Y ⥤ Z} {F : A ⥤ C} {G : B ⥤ C}

/-- Explicit inverse data for a categorical cospan transformation. The unit and counit live in
the categories of endotransformations of the source and target cospans; no triangle identity is
required at this layer. -/
structure QuasiInverse (ψ : CatCospanTransform H I F G) where
  /-- The inverse cospan transformation. -/
  inverse : CatCospanTransform F G H I
  /-- The comparison from the identity source transformation to the forward-inverse composite. -/
  unitIso : CatCospanTransform.id H I ≅ ψ.comp inverse
  /-- The comparison from the inverse-forward composite to the identity target transformation. -/
  counitIso : inverse.comp ψ ≅ CatCospanTransform.id F G

namespace QuasiInverse

variable {ψ : CatCospanTransform H I F G}

/-- Reverse explicit inverse data for a cospan transformation. -/
def symm (e : QuasiInverse ψ) : QuasiInverse e.inverse where
  inverse := ψ
  unitIso := e.counitIso.symm
  counitIso := e.unitIso.symm

/-- Reversing cospan quasi-inverse data selects the original transformation as inverse. -/
@[simp]
theorem symm_inverse (e : QuasiInverse ψ) :
    e.symm.inverse = ψ := sorry

/-- Reversing cospan quasi-inverse data uses the inverse counit as its unit. -/
@[simp]
theorem symm_unitIso (e : QuasiInverse ψ) :
    e.symm.unitIso = e.counitIso.symm := sorry

/-- Reversing cospan quasi-inverse data uses the inverse unit as its counit. -/
@[simp]
theorem symm_counitIso (e : QuasiInverse ψ) :
    e.symm.counitIso = e.unitIso.symm := sorry

/-- The unit induced on categorical-pullback maps by explicit inverse cospan data. -/
def mapUnitIso (e : QuasiInverse ψ) :
    𝟭 (H ⊡ I) ≅
      CategoricalPullback.map ψ ⋙ CategoricalPullback.map e.inverse :=
  (CategoricalPullback.mapIdIso (H := H) (I := I)).symm ≪≫
    CategoricalPullback.mapNatIso e.unitIso ≪≫
      CategoricalPullback.mapCompIso ψ e.inverse

/-- The counit induced on categorical-pullback maps by explicit inverse cospan data. -/
def mapCounitIso (e : QuasiInverse ψ) :
    CategoricalPullback.map e.inverse ⋙ CategoricalPullback.map ψ ≅
      𝟭 (F ⊡ G) :=
  (CategoricalPullback.mapCompIso e.inverse ψ).symm ≪≫
    CategoricalPullback.mapNatIso e.counitIso ≪≫
      CategoricalPullback.mapIdIso

/-- The left projection of the forward component of the induced pullback-map unit. -/
@[simp]
theorem mapUnitIso.hom.app.fst (e : QuasiInverse ψ) (P : H ⊡ I) :
    ((e.mapUnitIso).hom.app P).fst =
      (Functor.rightUnitor (π₁ H I)).inv.app P ≫
        e.unitIso.hom.left.app P.fst ≫
          (Functor.associator (π₁ H I) ψ.left e.inverse.left).inv.app P := sorry

/-- The right projection of the forward component of the induced pullback-map unit. -/
@[simp]
theorem mapUnitIso.hom.app.snd (e : QuasiInverse ψ) (P : H ⊡ I) :
    ((e.mapUnitIso).hom.app P).snd =
      (Functor.rightUnitor (π₂ H I)).inv.app P ≫
        e.unitIso.hom.right.app P.snd ≫
          (Functor.associator (π₂ H I) ψ.right e.inverse.right).inv.app P := sorry

/-- The left projection of the inverse component of the induced pullback-map unit. -/
@[simp]
theorem mapUnitIso.inv.app.fst (e : QuasiInverse ψ) (P : H ⊡ I) :
    ((e.mapUnitIso).inv.app P).fst =
      (Functor.associator (π₁ H I) ψ.left e.inverse.left).hom.app P ≫
        e.unitIso.inv.left.app P.fst ≫
          (Functor.rightUnitor (π₁ H I)).hom.app P := sorry

/-- The right projection of the inverse component of the induced pullback-map unit. -/
@[simp]
theorem mapUnitIso.inv.app.snd (e : QuasiInverse ψ) (P : H ⊡ I) :
    ((e.mapUnitIso).inv.app P).snd =
      (Functor.associator (π₂ H I) ψ.right e.inverse.right).hom.app P ≫
        e.unitIso.inv.right.app P.snd ≫
          (Functor.rightUnitor (π₂ H I)).hom.app P := sorry

/-- The left projection of the forward component of the induced pullback-map counit. -/
@[simp]
theorem mapCounitIso.hom.app.fst (e : QuasiInverse ψ) (P : F ⊡ G) :
    ((e.mapCounitIso).hom.app P).fst =
      (Functor.associator (π₁ F G) e.inverse.left ψ.left).hom.app P ≫
        e.counitIso.hom.left.app P.fst ≫
          (Functor.rightUnitor (π₁ F G)).hom.app P := sorry

/-- The right projection of the forward component of the induced pullback-map counit. -/
@[simp]
theorem mapCounitIso.hom.app.snd (e : QuasiInverse ψ) (P : F ⊡ G) :
    ((e.mapCounitIso).hom.app P).snd =
      (Functor.associator (π₂ F G) e.inverse.right ψ.right).hom.app P ≫
        e.counitIso.hom.right.app P.snd ≫
          (Functor.rightUnitor (π₂ F G)).hom.app P := sorry

/-- The left projection of the inverse component of the induced pullback-map counit. -/
@[simp]
theorem mapCounitIso.inv.app.fst (e : QuasiInverse ψ) (P : F ⊡ G) :
    ((e.mapCounitIso).inv.app P).fst =
      (Functor.rightUnitor (π₁ F G)).inv.app P ≫
        e.counitIso.inv.left.app P.fst ≫
          (Functor.associator (π₁ F G) e.inverse.left ψ.left).inv.app P := sorry

/-- The right projection of the inverse component of the induced pullback-map counit. -/
@[simp]
theorem mapCounitIso.inv.app.snd (e : QuasiInverse ψ) (P : F ⊡ G) :
    ((e.mapCounitIso).inv.app P).snd =
      (Functor.rightUnitor (π₂ F G)).inv.app P ≫
        e.counitIso.inv.right.app P.snd ≫
          (Functor.associator (π₂ F G) e.inverse.right ψ.right).inv.app P := sorry

/-- Explicit inverse data for a cospan transformation induce explicit quasi-inverse data for its
map between categorical pullbacks. -/
def toMapQuasiInverse (e : QuasiInverse ψ) :
    Functor.QuasiInverse (CategoricalPullback.map ψ) where
  inverse := CategoricalPullback.map e.inverse
  unitIso := e.mapUnitIso
  counitIso := e.mapCounitIso

/-- The inverse functor selected by `toMapQuasiInverse` is induced by the inverse cospan
transformation. -/
@[simp]
theorem toMapQuasiInverse.inverse (e : QuasiInverse ψ) :
    e.toMapQuasiInverse.inverse = CategoricalPullback.map e.inverse := sorry

/-- `toMapQuasiInverse` retains the induced pullback-map unit. -/
@[simp]
theorem toMapQuasiInverse.unitIso (e : QuasiInverse ψ) :
    e.toMapQuasiInverse.unitIso = e.mapUnitIso := sorry

/-- `toMapQuasiInverse` retains the induced pullback-map counit. -/
@[simp]
theorem toMapQuasiInverse.counitIso (e : QuasiInverse ψ) :
    e.toMapQuasiInverse.counitIso = e.mapCounitIso := sorry

/-- A cospan transformation with explicit quasi-inverse data induces an equivalence functor on
categorical pullbacks. -/
theorem mapIsEquivalence (e : QuasiInverse ψ) :
    (CategoricalPullback.map ψ).IsEquivalence := sorry

/-- A cospan transformation with explicit inverse data induces an equivalence between the
corresponding categorical pullbacks. -/
def mapEquivalence (e : QuasiInverse ψ) : H ⊡ I ≌ F ⊡ G :=
  e.toMapQuasiInverse.adjointifyUnit

/-- The forward functor of the induced pullback equivalence is the map of the original cospan
transformation. -/
@[simp]
theorem mapEquivalence.functor (e : QuasiInverse ψ) :
    e.mapEquivalence.functor = CategoricalPullback.map ψ := sorry

/-- The inverse functor of the induced pullback equivalence is the map of the inverse cospan
transformation. -/
@[simp]
theorem mapEquivalence.inverse (e : QuasiInverse ψ) :
    e.mapEquivalence.inverse = CategoricalPullback.map e.inverse := sorry

/-- The induced pullback equivalence retains the explicit pullback-map counit. -/
@[simp]
theorem mapEquivalence.counitIso (e : QuasiInverse ψ) :
    e.mapEquivalence.counitIso = e.mapCounitIso := sorry

/-- The unit of the induced pullback equivalence is the canonical adjointification of the
explicit pullback-map unit against its counit. -/
theorem mapEquivalence.unitIso (e : QuasiInverse ψ) :
    e.mapEquivalence.unitIso =
      Equivalence.adjointifyη e.mapUnitIso e.mapCounitIso := sorry

end QuasiInverse

end Limits.CatCospanTransform

end CategoryTheory
