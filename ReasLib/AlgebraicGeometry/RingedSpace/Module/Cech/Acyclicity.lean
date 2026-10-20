module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Comparison
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.Topology.Sheaf.Cohomology.Cech
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech comparison under finite-intersection acyclicity

The acyclicity condition is an object property of a module sheaf and an indexed open family.  The
comparison theorem selects one normalized derived comparison whose projections at that sheaf are
simultaneously invertible; it makes no assertion about arbitrary derived morphisms.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

variable {X : RingedSpace.{u}} {ι : Type u}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- A module is acyclic on the nonempty finite intersections of an indexed family of opens when
its positive-degree module cohomology vanishes on each such intersection. -/
@[stacks 01ET "acyclicity on finite Cech intersections"]
def IsAcyclicOnIntersections (𝒰 : ι → Opens X.carrier) (F : X.Modules) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
    IsZero (moduleCohomologyAtOpen
      (TopCat.Presheaf.Cech.intersection 𝒰 σ) F q)

/-- A module is underlying-acyclic on the nonempty finite intersections of an indexed family of
opens when the positive-degree cohomology of its underlying additive sheaf vanishes there. -/
@[stacks 01ET "underlying additive acyclicity on finite Cech intersections"]
def IsUnderlyingAcyclicOnIntersections
    (𝒰 : ι → Opens X.carrier) (F : X.Modules) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (n : ℕ) (σ : Fin (n + 1) → ι),
    IsZero (((moduleUnderlyingSheaf X).obj F).H' q
      (TopCat.Presheaf.Cech.intersection 𝒰 σ))

namespace IsAcyclicOnIntersections

omit [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
  [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})] in
/-- Unpack module-valued acyclicity at one finite intersection. -/
@[stacks 01ET "module-valued finite-intersection vanishing"]
theorem isZero
    {𝒰 : ι → Opens X.carrier} {F : X.Modules}
    (hF : IsAcyclicOnIntersections 𝒰 F) {q : ℕ} (hq : 0 < q)
    (n : ℕ) (σ : Fin (n + 1) → ι) :
    IsZero (moduleCohomologyAtOpen
      (TopCat.Presheaf.Cech.intersection 𝒰 σ) F q) := sorry

/-- The module and underlying-additive formulations are canonically equivalent. -/
@[stacks 01ET "module/additive finite-intersection acyclicity bridge"]
theorem iff_underlying
    (𝒰 : ι → Opens X.carrier) (F : X.Modules) :
    IsAcyclicOnIntersections 𝒰 F ↔
      IsUnderlyingAcyclicOnIntersections 𝒰 F := sorry

/-- Underlying additive acyclicity on finite intersections implies module-valued acyclicity. -/
@[stacks 01ET "underlying-to-module finite-intersection acyclicity"]
theorem of_underlying
    {𝒰 : ι → Opens X.carrier} {F : X.Modules}
    (hF : IsUnderlyingAcyclicOnIntersections 𝒰 F) :
    IsAcyclicOnIntersections 𝒰 F := sorry

/-- Finite-intersection acyclicity yields a normalized Čech-to-derived comparison that is
invertible at the given module. -/
@[stacks 01ET "Cech comparison under finite-intersection acyclicity"]
theorem exists_comparison
    {U : Opens X.carrier} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    {F : X.Modules} (hF : IsAcyclicOnIntersections 𝒰 F) :
    ∃ comparison : Comparison U (Opens.Cover.overFamily U 𝒰 h𝒰),
      Comparison.IsNormalized U (Opens.Cover.overFamily U 𝒰 h𝒰) comparison ∧
        Comparison.IsIsoAt U (Opens.Cover.overFamily U 𝒰 h𝒰) comparison F := sorry

/-- If a module is acyclic on every nonempty finite intersection of an open cover, then its Čech
cohomology is isomorphic to its cohomology on the covered open. -/
@[stacks 01ET "Cech cohomology and sheaf cohomology on an acyclic cover"]
theorem isIsomorphic_cohomology
    {U : Opens X.carrier} (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    {F : X.Modules} (hF : IsAcyclicOnIntersections 𝒰 F) (p : ℕ) :
    IsIsomorphic
      (cohomology U (Opens.Cover.overFamily U 𝒰 h𝒰) F p)
      (moduleCohomologyAtOpen U F p) := sorry

end IsAcyclicOnIntersections

end AlgebraicGeometry.RingedSpace.ModuleCech
