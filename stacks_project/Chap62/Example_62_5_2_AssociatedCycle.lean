/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle.FiberFamily

/-!
# Associated cycle families of quasi-coherent modules

This file associates to a quasi-coherent finite-type module of bounded fibrewise
support dimension the family of `r`-cycles on the scheme-theoretic fibres given
by the associated cycle of each fibre pullback.
-/

open CategoryTheory AlgebraicGeometry

universe u


/- The promoted shared API is re-exported here for source-facing compatibility. -/
#check (Scheme.Hom.fiberModule :
  {X S : Scheme.{u}} → (f : X ⟶ S) → (F : X.Modules) → (s : S) →
    (f.fiber s).Modules)
#check (Scheme.Hom.fiberModule_def :
  {X S : Scheme.{u}} → (f : X ⟶ S) → (F : X.Modules) → (s : S) →
    f.fiberModule F s = (Scheme.Modules.pullback (f.fiberι s)).obj F)
#check (Scheme.Hom.fiberModuleSupportDimensionLE :
  {X S : Scheme.{u}} → (f : X ⟶ S) → (F : X.Modules) → (r : ℕ) → Prop)
#check (Scheme.Hom.fiberModuleSupportDimensionLE_def :
  {X S : Scheme.{u}} → (f : X ⟶ S) → (F : X.Modules) → (r : ℕ) →
    f.fiberModuleSupportDimensionLE F r ↔
      ∀ s : S,
        topologicalKrullDim (Scheme.Modules.moduleSupport (f.fiberModule F s)) ≤
          (r : WithBot ℕ∞))
#check (Scheme.Hom.instIsCoherentFiberModule :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] →
    (F : X.Modules) → [F.IsQuasicoherent] → [F.IsFiniteType] → (s : S) →
      (f.fiberModule F s).IsCoherent)
#check (Scheme.Hom.moduleFiberCycleFamily :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] →
    (F : X.Modules) → [F.IsQuasicoherent] → [F.IsFiniteType] →
    (r : ℕ) → f.fiberModuleSupportDimensionLE F r → f.FiberCycleFamily (r : ℤ))
#check (Scheme.Hom.moduleFiberCycleFamily_apply :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] →
    (F : X.Modules) → [F.IsQuasicoherent] → [F.IsFiniteType] → (r : ℕ) →
    (hF : f.fiberModuleSupportDimensionLE F r) → (s : S) →
    Scheme.Hom.moduleFiberCycleFamily f F r hF s =
      Scheme.Modules.relativeAssociatedCycle (f.fiberToSpecResidueField s) (fun _ ↦ 0)
        (f.fiberModule F s) (r : ℤ))
#check (Scheme.Hom.moduleFiberCycleFamily_spec :
  {X S : Scheme.{u}} → (f : X ⟶ S) → [LocallyOfFiniteType f] →
    (F : X.Modules) → [F.IsQuasicoherent] → [F.IsFiniteType] → (r : ℕ) →
    (hF : f.fiberModuleSupportDimensionLE F r) → (s : S) →
    Scheme.Hom.moduleFiberCycleFamily f F r hF s =
      Scheme.Modules.relativeAssociatedCycle (f.fiberToSpecResidueField s) (fun _ ↦ 0)
        ((Scheme.Modules.pullback (f.fiberι s)).obj F) (r : ℤ))
