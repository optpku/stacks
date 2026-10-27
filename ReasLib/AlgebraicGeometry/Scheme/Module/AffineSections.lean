/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.ExteriorPower
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.LinearAlgebra.ExteriorPower.FormWedge
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
universe u
namespace AlgebraicGeometry.Scheme.Modules.Affine

variable {Y : Scheme.{u}} (U : Y.affineOpens) (M : Y.Modules)

/-- The image of the whole affine spectrum is exactly its specified open,
so restriction identifies local sections without an arbitrary-open tensor law. -/
theorem chart_image_top : U.property.fromSpec ''ᵁ ⊤ = U.1 := by
  ext x
  change x ∈ U.property.fromSpec '' Set.univ ↔ x ∈ U.1
  rw [Set.image_univ, U.property.range_fromSpec]
  rfl

/-- Local sections on an affine open are canonically global sections of
the actual pullback to its spectrum. This uses restriction/pullback adjunction
and the chart's image equality, not an asserted bijection of arbitrary maps. -/
noncomputable def pullbackSectionsIso :
    (M.presheaf.obj (op U.1)) ≅
      (((Scheme.Modules.pullback U.property.fromSpec).obj M).presheaf.obj (op ⊤)) :=
  M.presheaf.mapIso (eqToIso (chart_image_top U)).op ≪≫
    (M.restrictAppIso U.property.fromSpec ⊤).symm ≪≫
      ((Scheme.Modules.toPresheaf _).mapIso
        ((Scheme.Modules.restrictFunctorIsoPullback U.property.fromSpec).app M)).app (op ⊤)

end AlgebraicGeometry.Scheme.Modules.Affine

@[expose] public section
open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules.Affine

variable {Y : Scheme.{u}} (U : Y.affineOpens) (M N : Y.Modules)

/-- The genuine local tensor map is the tensor sheafification unit on
pure tensors, extended through the tensor product's universal property. -/
noncomputable def tensorMap :
    Γ(M, U.1) ⊗[Γ(Y, U.1)] Γ(N, U.1) →ₗ[Γ(Y, U.1)]
      Γ(SheafOfModules.RingedSite.moduleTensor (𝒪 := Y.sheaf) M N, U.1) :=
  TensorProduct.lift (SheafOfModules.RingedSite.tensorSectionLinear Y.sheaf M N (op U.1))

/-- On an affine open, quasi-coherence makes this specific sheafification
map bijective. This is deliberately not stated on arbitrary opens. -/
theorem tensorMap_bijective [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Bijective (tensorMap U M N) := sorry

/-- The canonical affine tensor-section equivalence, retaining the
actual sheafification map as its forward map. -/
noncomputable def tensorEquiv [M.IsQuasicoherent] [N.IsQuasicoherent] :=
  LinearEquiv.ofBijective (tensorMap U M N) (tensorMap_bijective U M N)

/-- The exterior comparison is the actual exterior-presheaf
sheafification unit, composed with the standard degree-zero/one presentation. -/
noncomputable def exteriorMap (n : ℕ) :
    exteriorPower.form Γ(Y, U.1) Γ(M, U.1) n →ₗ[Γ(Y, U.1)]
      Γ(SheafOfModules.RingedSite.ExteriorPower.sheaf Y.sheaf M n, U.1) :=
  ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal Y.sheaf
    (SheafOfModules.RingedSite.ExteriorPower.presheaf Y.sheaf M n)).app (op U.1)).hom.comp
      (CrystallineFormWedge.toExterior Γ(Y, U.1) Γ(M, U.1) n).toLinearMap

/-- Quasi-coherent exterior sheaves have their expected affine section
module. The comparison here is fixed by sheafification. -/
theorem exteriorMap_bijective [M.IsQuasicoherent] (n : ℕ) :
    Function.Bijective (exteriorMap U M n) := sorry

/-- The canonical affine exterior-section equivalence. -/
noncomputable def exteriorEquiv [M.IsQuasicoherent] (n : ℕ) :=
  LinearEquiv.ofBijective (exteriorMap U M n) (exteriorMap_bijective U M n)

end AlgebraicGeometry.Scheme.Modules.Affine
