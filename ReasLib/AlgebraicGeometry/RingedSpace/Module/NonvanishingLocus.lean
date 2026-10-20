/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Nonvanishing loci of module sections

The definition is made at the ringed-space level because it only uses the local stalk rings and
the germs of a global module section.  Openness and invertible-module consequences live in
`RingedSpace.Module.NonvanishingOpen`.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

section Nonvanishing

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- The points where the germ of a global `𝒪_X`-module section does not belong to
`𝔪_x ℒ_x`. -/
@[stacks 01CY "nonvanishing locus"]
def sectionNonvanishingLocus (ℒ : X.Modules) (s : ℒ.sections) : Set X :=
  {x | (TopCat.Presheaf.Γgerm ℒ.val.presheaf x (s.1 (Opposite.op ⊤))) ∉
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (↑(RingedSpace.stalkModuleCat ℒ x))))}

end Nonvanishing

end AlgebraicGeometry.RingedSpace
