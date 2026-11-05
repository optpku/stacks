/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Finite
public import Mathlib.CategoryTheory.Sites.Point.Basic
public import Mathlib.CategoryTheory.Sites.Point.Over
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.RingTheory.Finiteness.Basic

@[expose] public section

universe u v w

namespace CategoryTheory.GrothendieckTopology.Point

open Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (point : GrothendieckTopology.Point.{w} J)
variable {A : Type*} [Category A] [HasColimitsOfSize.{w, w} A]

/-- A constant presheaf has the prescribed fibre, since the category of
pointed neighbourhoods is connected. The two maps are colimit universal maps. -/
noncomputable def constantPresheafFiberIso (E : A) :
    point.presheafFiber.obj ((Functor.const Cᵒᵖ).obj E) ≅ E := by
  letI : IsConnected point.fiber.Elementsᵒᵖ := inferInstance
  exact (point.isColimitPresheafFiberCocone ((Functor.const Cᵒᵖ).obj E)).coconePointUniqueUpToIso
    (isColimitConstCocone point.fiber.Elementsᵒᵖ E)

@[reassoc (attr := simp)]
theorem toPresheafFiber_constantPresheafFiberIso_hom (E : A) (U : C)
    (x : point.fiber.obj U) :
    point.toPresheafFiber U x ((Functor.const Cᵒᵖ).obj E) ≫
      (point.constantPresheafFiberIso E).hom = 𝟙 E := by
  exact IsColimit.comp_coconePointUniqueUpToIso_hom
    (point.isColimitPresheafFiberCocone ((Functor.const Cᵒᵖ).obj E))
    (isColimitConstCocone point.fiber.Elementsᵒᵖ E)
    (Opposite.op (point.fiber.elementsMk U x))

/-- The constant-presheaf fibre identifications are natural in their values. -/
noncomputable def constantPresheafCompFiberIso :
    Functor.const Cᵒᵖ ⋙ point.presheafFiber (A := A) ≅ 𝟭 A :=
  NatIso.ofComponents point.constantPresheafFiberIso (by
    intro E E' g
    apply point.presheafFiber_hom_ext
    intro U x
    change point.toPresheafFiber U x ((Functor.const Cᵒᵖ).obj E) ≫
      point.presheafFiber.map ((Functor.const Cᵒᵖ).map g) ≫
        (point.constantPresheafFiberIso E').hom =
      point.toPresheafFiber U x ((Functor.const Cᵒᵖ).obj E) ≫
        (point.constantPresheafFiberIso E).hom ≫ g
    rw [point.toPresheafFiber_naturality_assoc]
    simp
    change g ≫ 𝟙 E' = 𝟙 E ≫ g
    simp only [Category.comp_id, Category.id_comp])

variable [HasWeakSheafify J A] [HasProducts.{w} A]

/-- Sheafification does not change the fibre of a constant presheaf. -/
noncomputable def constantSheafFiberIso (E : A) :
    point.sheafFiber.obj ((constantSheaf J A).obj E) ≅ E :=
  (point.presheafToSheafCompSheafFiberIso A).app ((Functor.const Cᵒᵖ).obj E) ≪≫
    point.constantPresheafFiberIso E

/-- A point is a left inverse to the constant-sheaf functor. -/
noncomputable def constantSheafCompFiberIso :
    constantSheaf J A ⋙ point.sheafFiber ≅ 𝟭 A :=
  Functor.isoWhiskerLeft (Functor.const Cᵒᵖ) (point.presheafToSheafCompSheafFiberIso A) ≪≫
    point.constantPresheafCompFiberIso

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Pointed objects of a slice are arrows into the corresponding fibre element.
Both functors preserve the underlying objects and maps. -/
def overFiberElementsEquivalence [LocallySmall.{w} C] {U : C}
    (x : point.fiber.obj U) :
    (point.over x).fiber.Elements ≌ Over (point.fiber.elementsMk U x) where
  functor.obj y := Over.mk (CategoryOfElements.homMk
    (point.fiber.elementsMk y.1.left y.2.1) _ y.1.hom
      (by rw [← FunctorToTypes.mem_fromOverSubfunctor_iff]; exact y.2.2))
  functor.map h := Over.homMk
    (CategoryOfElements.homMk _ _ h.1.left (congrArg Subtype.val h.2))
  inverse.obj y := Functor.elementsMk _ (Over.mk y.hom.1) ⟨y.left.2, by
    rw [FunctorToTypes.mem_fromOverSubfunctor_iff]; exact y.hom.2⟩
  inverse.map h := CategoryOfElements.homMk _ _
    (Over.homMk h.left.1 (congrArg Subtype.val (Over.w h))) (by cat_disch)
  unitIso := Iso.refl _
  counitIso := Iso.refl _
  functor_unitIso_comp _ := by simp; rfl

set_option backward.isDefEq.respectTransparency false in
/-- Restricting to a pointed slice leaves the sheaf fibre unchanged. The
forgetful functor on pointed neighbourhoods is initial because they are cofiltered. -/
noncomputable def overSheafFiberIso [LocallySmall.{w} C] {U : C}
    (x : point.fiber.obj U) (F : Sheaf J A) :
    (point.over x).sheafFiber.obj (F.over U) ≅ point.sheafFiber.obj F := by
  let Q := (overFiberElementsEquivalence point x).functor ⋙
    Over.forget (point.fiber.elementsMk U x)
  exact Functor.Final.colimitIso Q.op ((CategoryOfElements.π point.fiber).op ⋙ F.obj)

omit [HasColimitsOfSize.{w, w} A] [HasWeakSheafify J A] [HasProducts.{w} A] in
set_option backward.isDefEq.respectTransparency false in
/-- A point lifts into one of the constant charts of a locally constant sheaf.
The witness comes from the point's covering axiom and the given charts. -/
theorem exists_constant_chart [LocallySmall.{w} C]
    [∀ U : C, HasWeakSheafify (J.over U) A]
    {P : A → Prop} {F : Sheaf J A} (hF : Sheaf.IsLocallyConstantWith P F) :
    ∃ (U : C) (x : point.fiber.obj U) (E : A), P E ∧
      Nonempty (F.over U ≅ (constantSheaf (J.over U) A).obj E) := by
  obtain ⟨⟨U, x⟩⟩ := IsCofiltered.nonempty (C := point.fiber.Elements)
  obtain ⟨I, V, hV, hcharts⟩ := hF.existsConstantCover U
  let Ψ := point.over x
  let x' : Ψ.fiber.obj (Over.mk (𝟙 U)) := ⟨x, by
    rw [FunctorToTypes.mem_fromOverSubfunctor_iff]
    change point.fiber.map (𝟙 U) x = x
    simp⟩
  obtain ⟨W, g, ⟨i, ⟨a⟩⟩, y, hy⟩ :=
    Ψ.jointly_surjective (Sieve.ofObjects V (Over.mk (𝟙 U)))
      (hV (Over.mk (𝟙 U))) x'
  obtain ⟨E, hE, he⟩ := hcharts i
  exact ⟨(V i).left, (Ψ.fiber.map a y).1, E, hE, he⟩

end CategoryTheory.GrothendieckTopology.Point

namespace CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule

open CategoryTheory.GrothendieckTopology.Point

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {Λ : Type w} [Ring Λ] [LocallySmall.{w} C]
variable [HasWeakSheafify J (ModuleCat.{w} Λ)]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]

/-- The fibre of a locally constant sheaf of finite-type modules is finite.
The module model is taken from a chart through the point, rather than chosen
from an unproved finite-generation assertion. -/
theorem finite_sheafFiber {F : Sheaf J (ModuleCat.{w} Λ)}
    (hF : IsFiniteTypeLocallyConstantModule F)
    (point : GrothendieckTopology.Point.{w} J) :
    Module.Finite Λ ((point.sheafFiber (A := ModuleCat.{w} Λ)).obj F) := by
  obtain ⟨U, x, M, hM, ⟨e⟩⟩ := point.exists_constant_chart hF
  letI := hM
  let e' := (point.overSheafFiberIso x F).symm ≪≫
    (point.over x).sheafFiber.mapIso e ≪≫ (point.over x).constantSheafFiberIso M
  exact Module.Finite.equiv e'.toLinearEquiv.symm

end CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule


namespace CategoryTheory.Sheaf.IsFiniteLocallyConstant

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [HasWeakSheafify J (Type w)]
variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]
variable {F : Sheaf J (Type w)}

/-- The fiber of a finite locally constant sheaf of sets at any supplied site point
is finite. -/
theorem finite_sheafFiber (hF : IsFiniteLocallyConstant F)
    (point : GrothendieckTopology.Point.{w} J) :
    Finite (point.sheafFiber.obj F) := sorry

/-- Fibers of finite locally constant sheaves at supplied site points carry
canonical finiteness instances. -/
instance instFiniteSheafFiber [hF : IsFiniteLocallyConstant F]
    (point : GrothendieckTopology.Point.{w} J) :
    Finite (point.sheafFiber.obj F) :=
  finite_sheafFiber hF point

end CategoryTheory.Sheaf.IsFiniteLocallyConstant
