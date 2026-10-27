/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Derived.QuasiCoherent

/-!
# Quasi-coherent derived objects with small cohomology

The enlarged chaotic affine presentation has effective module universe `u` when
all sections of its cohomology modules are `u`-small.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} (X : GroupoidsOver S)

/-- Comparison-map quasi-coherence together with sectionwise `u`-small cohomology
on the chaotic affine site. -/
abbrev smallQCProperty : ObjectProperty
    (RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) :=
  fun K ↦ qcProperty X K ∧
    ∀ (n : ℤ) (U : (affineSite X)ᵒᵖ),
      Small.{u} (((@DerivedCategory.homologyFunctor
        (RingedSite.ModuleCat.{u + 1}
          (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) _ _
        (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
          (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) n).obj K).val.obj U)

/-- The full subcategory of comparison-map quasi-coherent derived objects with
sectionwise `u`-small cohomology. -/
abbrev SmallQC := (smallQCProperty X).FullSubcategory

/-- Membership in the small quasi-coherent subcategory is comparison-map
quasi-coherence together with smallness of every cohomology section. -/
theorem mem_smallQC_iff
    (K : RingedSite.Hom.ModuleDerived.{u + 1}
      (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) :
    smallQCProperty X K ↔ qcProperty X K ∧
      ∀ (n : ℤ) (U : (affineSite X)ᵒᵖ),
        Small.{u} (((@DerivedCategory.homologyFunctor
          (RingedSite.ModuleCat.{u + 1}
            (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) _ _
          (RingedSite.Hom.moduleCat_hasDerivedCategory.{u + 1}
            (RingedSite.ofCommRingSheaf ⊥ (affineStructureSheaf X))) n).obj K).val.obj U) := sorry

/-- Comparison-map quasi-coherence with sectionwise small cohomology is a
triangulated object property. -/
instance smallQCPropertyIsTriangulated : (smallQCProperty X).IsTriangulated := sorry

namespace SmallQC

/-- The inclusion of small quasi-coherent derived objects into the unrestricted
quasi-coherent derived category. -/
def inclusion : SmallQC X ⥤ QC X :=
  ObjectProperty.ιOfLE (fun _ h ↦ h.1)

end SmallQC

end AlgebraicGeometry.GroupoidsOver
