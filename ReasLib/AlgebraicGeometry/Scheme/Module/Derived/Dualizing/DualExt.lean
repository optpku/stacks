/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.DualExt
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.NormalizationDegree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Locality
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Normalized.Ext

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IsDualizingComplex

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
variable (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
variable {ω : RingedSpace.ModuleDerived X.toRingedSpace}
variable (hω : Scheme.IsDualizingComplex ω)
variable (F : X.Modules) [hF : F.IsCoherent]

include hω hF

/-- Each dual Ext sheaf of a coherent module against a dualizing complex is coherent. -/
theorem dualExt_isCoherent (i : ℤ) :
    (RingedSpace.DualExt.sheaf H F ω i).IsCoherent := sorry

/-- A nonzero dual Ext stalk occurs between the normalization degree and that
degree plus the support dimension of the original stalk. -/
theorem dualExt_nonzero_degreeBounds
    (δ : X → ℤ) (hδ : IsStalkNormalizationDegreeFunction ω δ)
    (x : X) (i : ℤ)
    (hi : ¬ IsZero
      (RingedSpace.stalkModuleCat (RingedSpace.DualExt.sheaf H F ω i) x)) :
    ∃ d : ℕ,
      Module.supportDim (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x) =
          .some (d : ℕ∞) ∧
        δ x ≤ i ∧ i ≤ δ x + d := sorry

/-- A nonzero shifted dual Ext stalk has support dimension at most its relative degree. -/
theorem dualExt_supportDim_le
    (δ : X → ℤ) (hδ : IsStalkNormalizationDegreeFunction ω δ)
    (x : X) (i : ℤ)
    (hi : ¬ IsZero
      (RingedSpace.stalkModuleCat
        (RingedSpace.DualExt.sheaf H F ω (i + δ x)) x)) :
    ∃ e : ℕ,
      Module.supportDim (X.presheaf.stalk x)
          (RingedSpace.stalkModuleCat
            (RingedSpace.DualExt.sheaf H F ω (i + δ x)) x) =
          .some (e : ℕ∞) ∧
        (e : ℤ) ≤ i := sorry

/-- The depth of a coherent stalk is the infimum of the nonnegative degrees
whose normalized dual Ext stalk is nonzero. -/
theorem depth_eq_sInf_nonzero_dualExt
    (δ : X → ℤ) (hδ : IsStalkNormalizationDegreeFunction ω δ) (x : X) :
    moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x) =
      sInf {d : ℕ∞ | ∃ n : ℕ, d = (n : ℕ∞) ∧
        ¬ IsZero
          (RingedSpace.stalkModuleCat
            (RingedSpace.DualExt.sheaf H F ω ((n : ℤ) + δ x)) x)} := sorry

/-- A point lies in cumulative dual Ext support through degree `i` exactly when
its stalk depth plus normalization degree is at most `i`. -/
theorem mem_dualExtSupportUpTo_iff_depth
    (δ : X → ℤ) (hδ : IsStalkNormalizationDegreeFunction ω δ)
    (x : X) (i : ℤ) :
    x ∈ RingedSpace.DualExt.supportUpTo H F ω i ↔
      ∃ d : ℕ,
        moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x) =
            (d : ℕ∞) ∧
          (d : ℤ) + δ x ≤ i := sorry

end AlgebraicGeometry.Scheme.IsDualizingComplex
