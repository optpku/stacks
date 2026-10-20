/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Algebra
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear

/-!
# Multiplication morphisms of graded algebra sheaves

Sectionwise multiplication in a graded algebra sheaf descends canonically to a morphism from
the tensor product of two homogeneous pieces.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.GradedAlgebraSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
variable [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {𝒪 : Sheaf J CommRingCat.{max u v}}
variable {ι : Type} [AddMonoid ι]

/-- The canonical tensor-product morphism induced by multiplication of two homogeneous pieces
of a graded algebra sheaf. -/
noncomputable def mulHom (𝒜 : GradedAlgebraSheaf 𝒪 ι) (a b : ι) :
    tensorObj (𝒜 a) (𝒜 b) ⟶ 𝒜 (a + b) :=
  SectionBilinearMap.hom
    ({ app := fun U ↦ 𝒜.mul U a b
       naturality := fun f x y ↦ 𝒜.map_mul f a b x y } :
      SectionBilinearMap 𝒪 (𝒜 a) (𝒜 b) (𝒜 (a + b)))

/-- The canonical multiplication morphism evaluates on a pure tensor section as the stored
graded multiplication. -/
@[simp]
theorem mulHom_tensorSection (𝒜 : GradedAlgebraSheaf 𝒪 ι) (a b : ι)
    (U : Cᵒᵖ) (x : (𝒜 a).val.obj U) (y : (𝒜 b).val.obj U) :
    ((mulHom 𝒜 a b).val.app U).hom (tensorSection 𝒪 U x y) =
      𝒜.mul U a b x y := sorry

end SheafOfModules.RingedSite.GradedAlgebraSheaf
