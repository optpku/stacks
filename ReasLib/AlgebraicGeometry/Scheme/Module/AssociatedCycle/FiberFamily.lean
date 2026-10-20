/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberSupportDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.LocalGeneration
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback

/-!
# Associated cycle families of quasi-coherent modules

This file associates to a quasi-coherent finite-type module of bounded fibrewise
support dimension the family of `r`-cycles on the scheme-theoretic fibres given
by the associated cycle of each fibre pullback.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The pullback of a module to the scheme-theoretic fibre over `s`. -/
noncomputable abbrev fiberModule (f : X ⟶ S) (F : X.Modules) (s : S) :
    (f.fiber s).Modules :=
  (Modules.pullback (f.fiberι s)).obj F

/-- The fibre module `F_s` is the pullback of `F` along the fibre inclusion. -/
theorem fiberModule_def (f : X ⟶ S) (F : X.Modules) (s : S) :
    f.fiberModule F s = (Modules.pullback (f.fiberι s)).obj F := sorry

/-- The fibrewise bound `dim(Supp(F_s)) ≤ r` on a module. -/
def fiberModuleSupportDimensionLE (f : X ⟶ S) (F : X.Modules) (r : ℕ) : Prop :=
  ∀ s : S, Modules.fiberSupportDimension f F s ≤ (r : WithBot ℕ∞)

/-- The fibrewise support-dimension bound is a bound on the topological Krull
dimension of the support of the fibre module. -/
theorem fiberModuleSupportDimensionLE_def (f : X ⟶ S) (F : X.Modules) (r : ℕ) :
    f.fiberModuleSupportDimensionLE F r ↔
      ∀ s : S,
        topologicalKrullDim (Modules.moduleSupport (f.fiberModule F s)) ≤
          (r : WithBot ℕ∞) := sorry

/-- The pullback of a quasi-coherent finite-type module to a fibre of a locally
finite-type morphism is coherent. -/
instance instIsCoherentFiberModule (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (s : S) :
    (f.fiberModule F s).IsCoherent := sorry

/-- The family of `r`-cycles on fibres of `X/S` associated to a quasi-coherent
finite-type module of fibrewise support dimension at most `r`. -/
noncomputable def moduleFiberCycleFamily (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r) :
    f.FiberCycleFamily (r : ℤ) :=
  fun s ↦ Modules.relativeAssociatedCycle (f.fiberToSpecResidueField s)
    (fun _ ↦ 0) (f.fiberModule F s) (r : ℤ)

/-- Evaluating the associated fibrewise cycle family recovers the relative
associated cycle of the fibre module. -/
theorem moduleFiberCycleFamily_apply (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r) (s : S) :
    moduleFiberCycleFamily f F r hF s =
      Modules.relativeAssociatedCycle (f.fiberToSpecResidueField s) (fun _ ↦ 0)
        (f.fiberModule F s) (r : ℤ) := sorry

/-- The associated fibrewise cycle family is `([F_s]_r)_{s ∈ S}`, where `F_s` is
the pullback of `F` to the fibre `X_s`. -/
theorem moduleFiberCycleFamily_spec (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (r : ℕ)
    (hF : f.fiberModuleSupportDimensionLE F r) (s : S) :
    moduleFiberCycleFamily f F r hF s =
      Modules.relativeAssociatedCycle (f.fiberToSpecResidueField s) (fun _ ↦ 0)
        ((Modules.pullback (f.fiberι s)).obj F) (r : ℤ) := sorry

end AlgebraicGeometry.Scheme.Hom
