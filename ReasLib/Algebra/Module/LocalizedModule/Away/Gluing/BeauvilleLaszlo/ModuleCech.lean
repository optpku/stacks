module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo

import Mathlib.Tactic.CrossRefAttribute

/-!
# The module Beauville-Laszlo Cech sequence

Tensoring the ring-level Beauville-Laszlo Cech sequence with a module and transporting along the
tensor unit and product-distribution isomorphisms gives the displayed module Cech sequence.

@stack 0F1R
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory ModuleCat MonoidalCategory
open scoped TensorProduct

section

variable {R : Type u} [CommRing R]
variable (R' : Type u) [CommRing R'] [Algebra R R']
variable (M : Type u) [AddCommGroup M] [Module R M]

/-- The tensor image of the ring-level Beauville-Laszlo Cech sequence. -/
@[stacks 0F1R "tensor image of the Beauville-Laszlo ring Cech sequence"]
noncomputable abbrev beauvilleLaszloModuleCechTensorImage (f : R) :
    ShortComplex (ModuleCat R) :=
  (beauvilleLaszloCechSequence (algebraMap R R') f).map (tensorLeft (of R M))

/-- The middle object of the tensor-image sequence is the tensor image of the product ring term. -/
theorem beauvilleLaszloModuleCechMiddleTensor_eq (f : R) :
    let _ : Algebra R R' := (algebraMap R R').toAlgebra
    (beauvilleLaszloModuleCechTensorImage R' M f).X₂ =
      (tensorLeft (of R M)).obj (of R (R' × Localization.Away f)) := sorry

/-- The canonical isomorphism supplied by the middle-object equality. -/
@[stacks 0F1R "middle-object comparison for the tensor-image Cech sequence"]
noncomputable abbrev beauvilleLaszloModuleCechMiddleTensorIso (f : R) :
    let _ : Algebra R R' := (algebraMap R R').toAlgebra
    (beauvilleLaszloModuleCechTensorImage R' M f).X₂ ≅
      (tensorLeft (of R M)).obj (of R (R' × Localization.Away f)) :=
  eqToIso (beauvilleLaszloModuleCechMiddleTensor_eq R' M f)

/-- Tensoring a module object on the left realizes the ordinary tensor-product module. -/
@[stacks 0F1R "tensor-left object as an ordinary tensor-product module"]
noncomputable def tensorLeft_obj_tensorProductIso
    (N : Type u) [AddCommGroup N] [Module R N] :
    (tensorLeft (of R M)).obj (of R N) ≅ of R (M ⊗[R] N) :=
  Iso.refl _

/-- The tensor-image middle object transported to a product of ordinary tensor products. -/
@[stacks 0F1R "canonical middle-object comparison for the module Cech sequence"]
noncomputable def beauvilleLaszloModuleCechCanonicalMiddleIso (f : R) :
    let _ : Algebra R R' := (algebraMap R R').toAlgebra
    (beauvilleLaszloModuleCechTensorImage R' M f).X₂ ≅
      of R ((M ⊗[R] R') × (M ⊗[R] Localization.Away f)) :=
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  (beauvilleLaszloModuleCechMiddleTensorIso R' M f) ≪≫
    (tensorLeft_obj_tensorProductIso (R := R) (M := M) (N := R' × Localization.Away f)) ≪≫
    (TensorProduct.prodRight R R M R' (Localization.Away f)).toModuleIso

/-- The displayed middle module in the module Beauville-Laszlo Cech sequence. -/
@[stacks 0F1R "middle module in the Beauville-Laszlo Cech sequence"]
abbrev beauvilleLaszloModuleCechMiddleModule (f : R) : Type u :=
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  (M ⊗[R] R') × (M ⊗[R] Localization.Away f)

/-- The canonical isomorphism from the tensor-image middle object to the displayed middle
module. -/
@[stacks 0F1R "displayed middle-object comparison for the module Cech sequence"]
noncomputable abbrev beauvilleLaszloModuleCechMiddleIso (f : R) :
    (beauvilleLaszloModuleCechTensorImage R' M f).X₂ ≅
      of R (beauvilleLaszloModuleCechMiddleModule R' M f) :=
  let _ : Algebra R R' := (algebraMap R R').toAlgebra
  beauvilleLaszloModuleCechCanonicalMiddleIso (R := R) (R' := R') (M := M) f

/-- The tensor-image left object identified with `M` by the right unitor. -/
@[stacks 0F1R "left-object comparison for the module Cech sequence"]
noncomputable abbrev beauvilleLaszloModuleCechLeftIso (f : R) :
    (beauvilleLaszloModuleCechTensorImage R' M f).X₁ ≅ of R M :=
  ρ_ (of R M)

/-- The transported left map into the displayed middle module. -/
@[stacks 0F1R "left map of the Beauville-Laszlo module Cech sequence"]
noncomputable abbrev beauvilleLaszloModuleCechAlpha (f : R) :
    M →ₗ[R] beauvilleLaszloModuleCechMiddleModule R' M f :=
  let tensorImage := beauvilleLaszloModuleCechTensorImage R' M f
  let leftIso : tensorImage.X₁ ≅ of R M := beauvilleLaszloModuleCechLeftIso R' M f
  let middleIso : tensorImage.X₂ ≅ of R (beauvilleLaszloModuleCechMiddleModule R' M f) :=
    beauvilleLaszloModuleCechMiddleIso R' M f
  (leftIso.inv ≫ tensorImage.f ≫ middleIso.hom).hom

/-- The transported right map out of the displayed middle module. -/
@[stacks 0F1R "right map of the Beauville-Laszlo module Cech sequence"]
noncomputable abbrev beauvilleLaszloModuleCechBeta (f : R) :
    beauvilleLaszloModuleCechMiddleModule R' M f →ₗ[R]
      (beauvilleLaszloModuleCechTensorImage R' M f).X₃ :=
  let tensorImage := beauvilleLaszloModuleCechTensorImage R' M f
  let middleIso : tensorImage.X₂ ≅ of R (beauvilleLaszloModuleCechMiddleModule R' M f) :=
    beauvilleLaszloModuleCechMiddleIso R' M f
  (middleIso.inv ≫ tensorImage.g).hom

/-- The transported module Beauville-Laszlo Cech maps compose to zero. -/
theorem beauvilleLaszloModuleCech_comp_eq_zero (f : R) :
    (beauvilleLaszloModuleCechBeta R' M f).comp (beauvilleLaszloModuleCechAlpha R' M f) =
      (0 : M →ₗ[R] (beauvilleLaszloModuleCechTensorImage R' M f).X₃) := sorry

/-- 15.91.9.1 (0F1R): the displayed sequence
`0 → M → (M ⊗[R] R') × (M ⊗[R] Localization.Away f) →
M ⊗[R] Localization.Away (algebraMap R R' f) → 0`, represented as a short complex in
`ModuleCat R`. -/
@[stacks 0F1R, stacks 0BNV "principal-adic module Cech sequence"]
noncomputable abbrev beauvilleLaszloModuleCechSequence (f : R) :
    ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk
    (beauvilleLaszloModuleCechAlpha R' M f)
    (beauvilleLaszloModuleCechBeta R' M f)
    (beauvilleLaszloModuleCech_comp_eq_zero R' M f)

end
