/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.DualExt
import StacksCheckRecall

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

/- Lemma 48.2.8 -/
@[stacks 0ECM] #check (AlgebraicGeometry.Scheme.IsDualizingComplex.dualExt_isCoherent :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      {ω : RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : Scheme.IsDualizingComplex ω) (F : X.Modules) [F.IsCoherent]
      (i : ℤ), (RingedSpace.DualExt.sheaf H F ω i).IsCoherent)

/- Lemma 48.2.8 (2) -/
@[stacks 0ECM]
#check (AlgebraicGeometry.Scheme.IsDualizingComplex.dualExt_nonzero_degreeBounds :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      {ω : RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : Scheme.IsDualizingComplex ω) (F : X.Modules) [F.IsCoherent]
      (δ : X → ℤ) (hδ : IsStalkNormalizationDegreeFunction ω δ)
      (x : X) (i : ℤ)
      (hi : ¬ IsZero (RingedSpace.stalkModuleCat
        (RingedSpace.DualExt.sheaf H F ω i) x)),
      ∃ d : ℕ, Module.supportDim (X.presheaf.stalk x)
        (RingedSpace.stalkModuleCat F x) = .some (d : ℕ∞) ∧
        δ x ≤ i ∧ i ≤ δ x + d)

/- Lemma 48.2.8 (3) -/
@[stacks 0ECM]
#check (AlgebraicGeometry.Scheme.IsDualizingComplex.dualExt_supportDim_le :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      {ω : RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : Scheme.IsDualizingComplex ω) (F : X.Modules) [F.IsCoherent]
      (δ : X → ℤ) (hδ : IsStalkNormalizationDegreeFunction ω δ)
      (x : X) (i : ℤ)
      (hi : ¬ IsZero (RingedSpace.stalkModuleCat
        (RingedSpace.DualExt.sheaf H F ω (i + δ x)) x)),
      ∃ e : ℕ, Module.supportDim (X.presheaf.stalk x)
        (RingedSpace.stalkModuleCat (RingedSpace.DualExt.sheaf H F ω (i + δ x)) x) =
        .some (e : ℕ∞) ∧ (e : ℤ) ≤ i)

/- Lemma 48.2.8 (4) -/
@[stacks 0ECM]
#check (AlgebraicGeometry.Scheme.IsDualizingComplex.depth_eq_sInf_nonzero_dualExt :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      {ω : RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : Scheme.IsDualizingComplex ω) (F : X.Modules) [F.IsCoherent]
      (δ : X → ℤ) (hδ : IsStalkNormalizationDegreeFunction ω δ) (x : X),
      moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x) =
        sInf {d : ℕ∞ | ∃ n : ℕ, d = (n : ℕ∞) ∧
          ¬ IsZero (RingedSpace.stalkModuleCat
            (RingedSpace.DualExt.sheaf H F ω ((n : ℤ) + δ x)) x)})

/- Lemma 48.2.8 (5) -/
@[stacks 0ECM]
#check (AlgebraicGeometry.Scheme.IsDualizingComplex.mem_dualExtSupportUpTo_iff_depth :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      {ω : RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : Scheme.IsDualizingComplex ω) (F : X.Modules) [F.IsCoherent]
      (δ : X → ℤ) (hδ : IsStalkNormalizationDegreeFunction ω δ)
      (x : X) (i : ℤ),
      x ∈ RingedSpace.DualExt.supportUpTo H F ω i ↔
        ∃ d : ℕ,
          moduleDepth (X.presheaf.stalk x) (RingedSpace.stalkModuleCat F x) =
            (d : ℕ∞) ∧ (d : ℤ) + δ x ≤ i)

end AlgebraicGeometry.Scheme.IsDualizingComplex
