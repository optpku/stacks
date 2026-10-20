/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FiniteFree
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Stalk
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Stalks of cohomology of derived modules

This leaf owns the stalk of a cohomology sheaf as a bundled module over the local stalk ring. It
also provides the pointwise finite-free predicate used by geometric loci.
-/

open AlgebraicGeometry
open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}

/-- The stalk at `x` of the degree-`i` cohomology sheaf of `E`, bundled over `𝒪_{X,x}`. -/
@[stacks 0GT1 "cohomology stalk"]
abbrev cohomologyStalk (E : ModuleDerived X) (i : ℤ) (x : X) :
    ModuleCat (X.presheaf.stalk x) :=
  RingedSpace.stalkModuleCat (cohomologySheaf E i) x

/-- The degree-`i` cohomology stalk of `E` at `x` is finite free over `𝒪_{X,x}`. -/
abbrev cohomologyStalkFiniteFree (E : ModuleDerived X) (i : ℤ) (x : X) : Prop :=
  ModuleCat.finiteFree (X.presheaf.stalk x) (cohomologyStalk E i x)

namespace Cohomology

/-- Points where every cohomology stalk of `E` is finite free. -/
def finiteFreeLocus (E : ModuleDerived X) : Set X :=
  {x | ∀ i : ℤ, cohomologyStalkFiniteFree E i x}

/-- Membership in the finite-free cohomology locus is the pointwise condition in every degree. -/
@[simp]
theorem mem_finiteFreeLocus_iff (E : ModuleDerived X) (x : X) :
    x ∈ finiteFreeLocus E ↔ ∀ i : ℤ, cohomologyStalkFiniteFree E i x := sorry

end Cohomology

end AlgebraicGeometry.RingedSpace.ModuleDerived
