/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Fundamental
public import ReasLib.AlgebraicGeometry.Scheme.Module.ZeroScheme.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction

/-!
# Zero cycles of sections

This file defines the cycle obtained by pushing the fundamental cycle of the zero scheme of a
section to the ambient scheme, both for absolute and relative dimension functions.
-/

@[expose] public section

open CategoryTheory Function
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

section Absolute

variable {Y : Scheme.{u}}

/-- The degree-`k` cycle of the zero scheme of `s`, pushed forward to `Y`. -/
noncomputable def zeroCycle [IsLocallyNoetherian Y]
    (d : Y → ℤ) (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) : AlgebraicCycle Y ℤ :=
  AlgebraicCycle.map (zeroSchemeι ℒ s) (d ∘ zeroSchemeι ℒ s) d
    (AlgebraicCycle.fundamental (d ∘ zeroSchemeι ℒ s) k)

/-- The zero cycle is the pushforward of the fundamental cycle of the zero scheme. -/
theorem zeroCycle_def [IsLocallyNoetherian Y]
    (d : Y → ℤ) (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) :
    zeroCycle d ℒ s k =
      AlgebraicCycle.map (zeroSchemeι ℒ s) (d ∘ zeroSchemeι ℒ s) d
        (AlgebraicCycle.fundamental (d ∘ zeroSchemeι ℒ s) k) := sorry

end Absolute

section Relative

variable {S Y : Scheme.{u}} (f : Y ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
variable (δ : S → ℤ) [IsDimensionFunction δ]

/-- The zero-section cycle measured by the relative dimension function induced by `f` and `δ`. -/
noncomputable def relativeZeroCycle (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) : AlgebraicCycle Y ℤ :=
  @zeroCycle Y (LocallyOfFiniteType.isLocallyNoetherian f)
    (f.relativeDimensionFunction δ) ℒ _ s k

/-- The relative zero cycle is the core zero cycle for `f.relativeDimensionFunction δ`. -/
theorem relativeZeroCycle_def (ℒ : Y.Modules) [Invertible ℒ]
    (s : ℒ.sections) (k : ℤ) :
    relativeZeroCycle f δ ℒ s k =
      @zeroCycle Y (LocallyOfFiniteType.isLocallyNoetherian f)
        (f.relativeDimensionFunction δ) ℒ _ s k := sorry

end Relative

end AlgebraicGeometry.Scheme.Modules
