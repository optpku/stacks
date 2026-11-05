module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Site
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.TensorUnit
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Tensor powers of module sheaves on ringed spaces

This file specializes the topology-independent tensor-power functor to a ringed space.  The
canonical monoidal structure and tensor-unit comparison are inferred from the opens site.
Standard local-property instances live in the generic `TensorPower.Properties` leaf and are
re-exported by the broad algebra-sheaf entry point.

## Main declarations

- `RingedSpace.TensorPower.functor X n`: the degree-`n` tensor-power endofunctor
- `RingedSpace.TensorPower.sheaf ℱ n`: the `n`th tensor power of `ℱ`
- `RingedSpace.TensorPower.map f n`: the induced morphism on degree-`n` tensor powers
- `RingedSpace.TensorPower.oneIso ℱ`: the canonical identification of the first tensor power
  with `ℱ`
- `RingedSpace.TensorPower.monoidalComparison ℱ n`: the comparison from the ambient monoidal
  tensor power
- `RingedSpace.TensorPower.monoidalComparison.inv ℱ n`: its structural recursive inverse
- `RingedSpace.TensorPower.monoidalComparison.iso ℱ n`: the two maps bundled as an isomorphism
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.TensorPower

variable {X : RingedSpace.{u}}

/-- The degree-`n` tensor-power endofunctor on module sheaves over `X`. -/
@[stacks 01CK "tensor-power functor on module sheaves"]
noncomputable def functor (X : RingedSpace.{u}) (n : ℕ) :
    X.Modules ⥤ X.Modules :=
  SheafOfModules.RingedSite.TensorPower.functor X.sheaf n

/-- The `n`th tensor power `TensorPower.sheaf ℱ n` of a module sheaf on `X`. -/
@[stacks 01CK "tensor power of a module sheaf"]
noncomputable abbrev sheaf (ℱ : X.Modules) (n : ℕ) : X.Modules :=
  SheafOfModules.RingedSite.TensorPower.sheaf X.sheaf ℱ n

/-- The morphism on degree-`n` tensor powers induced by a morphism of module sheaves. -/
@[stacks 01CK "morphism on tensor powers of module sheaves"]
noncomputable abbrev map {ℱ 𝒢 : X.Modules}
    (f : ℱ ⟶ 𝒢) (n : ℕ) : sheaf ℱ n ⟶ sheaf 𝒢 n :=
  SheafOfModules.RingedSite.TensorPower.map X.sheaf f n

/-- The zeroth tensor power is the structure module. -/
@[simp, stacks 01CK "zeroth tensor power of a ringed-space module sheaf"]
theorem zero (ℱ : X.Modules) :
    sheaf ℱ 0 = (SheafOfModules.unit X.ringCatSheaf : X.Modules) := sorry

/-- Tensor powers satisfy the left-recursive successor formula. -/
@[simp, stacks 01CK "successor tensor power of a ringed-space module sheaf"]
theorem succ (ℱ : X.Modules) (n : ℕ) :
    sheaf ℱ (n + 1) = tensorObj ℱ (sheaf ℱ n) := sorry

/-- The zeroth tensor-power map is the identity of the structure module. -/
@[simp, stacks 01CK "zeroth tensor-power map of a ringed-space module sheaf"]
theorem map_zero {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    map f 0 = 𝟙 _ := sorry

/-- Tensor-power maps satisfy the left-recursive successor formula. -/
@[simp, stacks 01CK "successor tensor-power map of a ringed-space module sheaf"]
theorem map_succ {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) (n : ℕ) :
    map f (n + 1) = f ⊗ₘ map f n := sorry

/-- The first tensor power of a module sheaf is canonically the module sheaf itself. -/
@[stacks 01CK "first tensor power of a module sheaf"]
noncomputable abbrev oneIso (ℱ : X.Modules) : sheaf ℱ 1 ≅ ℱ :=
  SheafOfModules.RingedSite.TensorPower.oneIso X.sheaf ℱ

/-- The canonical comparison from the ambient monoidal tensor power to the ringed-space tensor
power whose zeroth term is the structure module. -/
@[stacks 01CK "monoidal comparison for ringed-space tensor powers"]
noncomputable abbrev monoidalComparison (ℱ : X.Modules) (n : ℕ) :
    tensorPower ℱ n ⟶ sheaf ℱ n :=
  SheafOfModules.RingedSite.TensorPower.monoidalComparison X.sheaf ℱ n

namespace monoidalComparison

/-- The structural inverse of the ringed-space tensor-power comparison. -/
@[stacks 01CK "inverse monoidal comparison for ringed-space tensor powers"]
noncomputable abbrev inv (ℱ : X.Modules) (n : ℕ) :
    sheaf ℱ n ⟶ tensorPower ℱ n :=
  SheafOfModules.RingedSite.TensorPower.monoidalComparison.inv X.sheaf ℱ n

/-- The ringed-space tensor-power comparison and its structural inverse as an isomorphism. -/
@[stacks 01CK "monoidal comparison isomorphism for ringed-space tensor powers"]
noncomputable abbrev iso (ℱ : X.Modules) (n : ℕ) :
    tensorPower ℱ n ≅ sheaf ℱ n :=
  SheafOfModules.RingedSite.TensorPower.monoidalComparison.iso X.sheaf ℱ n

/-- The forward map of the ringed-space tensor-power comparison isomorphism is the canonical
comparison. -/
@[simp, stacks 01CK "ringed-space monoidal comparison isomorphism hom"]
theorem iso_hom (ℱ : X.Modules) (n : ℕ) :
    (iso ℱ n).hom = monoidalComparison ℱ n := sorry

/-- The inverse map of the ringed-space tensor-power comparison isomorphism is the structural
inverse. -/
@[simp, stacks 01CK "ringed-space monoidal comparison isomorphism inverse"]
theorem iso_inv (ℱ : X.Modules) (n : ℕ) :
    (iso ℱ n).inv = inv ℱ n := sorry

/-- The forward maps of the ringed-space tensor-power comparison isomorphisms are natural in the
module sheaf. -/
@[stacks 01CK "naturality of ringed-space tensor-power comparison isomorphisms"]
theorem iso_naturality {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) (n : ℕ) :
    tensorPowerMap f n ≫ (iso 𝒢 n).hom =
      (iso ℱ n).hom ≫ map f n := sorry

end monoidalComparison

/-- In degree zero, the structural inverse is the map from the structure module to the ambient
tensor unit. -/
@[simp, stacks 01CK "inverse ringed-space monoidal comparison in degree zero"]
theorem monoidalComparison_inv_zero (ℱ : X.Modules) :
    monoidalComparison.inv ℱ 0 = RingedSpace.unitModuleToTensorUnit X := sorry

/-- The structural inverse comparison is recursive in successor degree. -/
@[simp, stacks 01CK "inverse ringed-space monoidal comparison in successor degree"]
theorem monoidalComparison_inv_succ (ℱ : X.Modules) (n : ℕ) :
    monoidalComparison.inv ℱ (n + 1) =
      𝟙 ℱ ⊗ₘ monoidalComparison.inv ℱ n := sorry

/-- In degree zero, the ringed-space tensor-power comparison is the tensor-unit comparison. -/
@[simp, stacks 01CK "ringed-space monoidal comparison in degree zero"]
theorem monoidalComparison_zero (ℱ : X.Modules) :
    monoidalComparison ℱ 0 = RingedSpace.tensorUnitToUnitModule X := sorry

/-- The ringed-space tensor-power comparison is recursive in successor degree. -/
@[simp, stacks 01CK "ringed-space monoidal comparison in successor degree"]
theorem monoidalComparison_succ (ℱ : X.Modules) (n : ℕ) :
    monoidalComparison ℱ (n + 1) = 𝟙 ℱ ⊗ₘ monoidalComparison ℱ n := sorry

/-- The ringed-space tensor-power comparison is natural in the module sheaf. -/
@[stacks 01CK "naturality of the ringed-space monoidal comparison"]
theorem monoidalComparison_naturality {ℱ 𝒢 : X.Modules}
    (f : ℱ ⟶ 𝒢) (n : ℕ) :
    tensorPowerMap f n ≫ monoidalComparison 𝒢 n =
      monoidalComparison ℱ n ≫ map f n := sorry

/-- The structural inverse comparison is natural in the module sheaf. -/
@[stacks 01CK "naturality of the inverse ringed-space monoidal comparison"]
theorem monoidalComparison_inv_naturality {ℱ 𝒢 : X.Modules}
    (f : ℱ ⟶ 𝒢) (n : ℕ) :
    map f n ≫ monoidalComparison.inv 𝒢 n =
      monoidalComparison.inv ℱ n ≫ tensorPowerMap f n := sorry

/-- The degree-`n` ringed-space comparisons assemble into a natural isomorphism of functors. -/
@[stacks 01CK "natural isomorphism of ringed-space tensor-power comparisons"]
noncomputable abbrev monoidalComparisonNatIso (n : ℕ) :
    tensorPowerFunctor X.Modules n ≅ functor X n :=
  SheafOfModules.RingedSite.TensorPower.monoidalComparisonNatIso X.sheaf n

end AlgebraicGeometry.RingedSpace.TensorPower

