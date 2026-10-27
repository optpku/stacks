/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.NaiveCotangent.Presentation.Ext

/-!
# Presentation witnesses for the Ext¹ deformation action

The representative includes its locally surjective polynomial presentation.
It is not a section onto the conormal of one arbitrarily fixed complex.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Sheaf
open SheafOfModules.RingedSite SheafOfModules.RingedSite.NaiveCotangent
open scoped DerivedExt

noncomputable section
universe c v w

namespace SheafOfModules.RingedSite.NaiveCotangent

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J CommRingCat.{w}]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [HasSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {A B : Sheaf J CommRingCat.{w}} (φ : A ⟶ B)
variable (G : SheafOfModules.{w} (ringSheaf J (Under.mk φ).right))
-- Local instance justification (defeq pin): all Ext and presentation maps use the standard derived quotient at the independent coefficient universe.
attribute [local instance] HasDerivedCategory.standard

/-- All presentation data and the exact derived equation representing an Ext¹ class. -/
structure ExtOnePresentation
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) where
  /-- The chosen generators on the site. -/
  generators : Sheaf J (Type w)
  /-- Evaluation of these generators in the target algebra. -/
  assignment : generators ⟶ FreeAlgebra.Presentation.generators (Under.mk φ)
  /-- The evaluation is an actual local presentation. -/
  locallySurjective : IsLocallySurjective (FreeAlgebra.evaluation (Under.mk φ) generators assignment).right
  /-- A morphism from the conormal of this presentation. -/
  conormalMap : (Presentation.ofGenerators generators assignment).X (-1) ⟶ G
  /-- The comparison to the source Ext¹ class; no unsupported inversion occurs. -/
  represents : Presentation.derivedComparison generators assignment ≫ ξ =
    conormalHomClass φ G generators assignment conormalMap

/-- Every Ext¹ class has a locally surjective presentation and a representing conormal map. -/
theorem exists_extOnePresentation
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    Nonempty (ExtOnePresentation φ G ξ) := by
  obtain ⟨E, α, hα, δ, hδ⟩ := exists_conormalHomClass φ G ξ
  exact ⟨⟨E, α, hα, δ, hδ⟩⟩

/-- Choose a fully specified presentation witness, not a bare inverse or a fixed-conormal map. -/
def extOnePresentation
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    ExtOnePresentation φ G ξ :=
  Classical.choice (exists_extOnePresentation φ G ξ)

/-- The selected witness retains the actual equation furnished by the canonical owner. -/
theorem extOnePresentation_represents
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    Presentation.derivedComparison (extOnePresentation φ G ξ).generators
      (extOnePresentation φ G ξ).assignment ≫ ξ =
    conormalHomClass φ G (extOnePresentation φ G ξ).generators
      (extOnePresentation φ G ξ).assignment (extOnePresentation φ G ξ).conormalMap :=
  (extOnePresentation φ G ξ).represents

/-- The selected presentation is locally surjective and its conormal map represents the class. -/
theorem extOnePresentation_spec
    (ξ : Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj (obj A (Under.mk φ)),
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj G))) :
    IsLocallySurjective (FreeAlgebra.evaluation (Under.mk φ)
      (extOnePresentation φ G ξ).generators (extOnePresentation φ G ξ).assignment).right ∧
    Presentation.derivedComparison (extOnePresentation φ G ξ).generators
      (extOnePresentation φ G ξ).assignment ≫ ξ =
      conormalHomClass φ G (extOnePresentation φ G ξ).generators
        (extOnePresentation φ G ξ).assignment (extOnePresentation φ G ξ).conormalMap :=
  ⟨(extOnePresentation φ G ξ).locallySurjective, (extOnePresentation φ G ξ).represents⟩

end SheafOfModules.RingedSite.NaiveCotangent

