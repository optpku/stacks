/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.SeparableClosure
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Characteristic.Prime
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting

/-!
# Weightings attached to relative zero-cycles

Fibrewise zero-cycles determine integer-valued functions by multiplying each
coefficient by the inseparable residue-field degree. Relative zero-cycles give
weightings, and on a quasi-compact source every weighting has a positive multiple
of this form, with a prime-power multiple in prime characteristic.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The integer-valued function attached to a family of fibrewise zero-cycles,
whose value at `x` is the coefficient of `f.asFiber x` in `α (f x)` multiplied
by the finite inseparable degree of `κ(x)` over `κ(f x)`. -/
noncomputable def weighting {X S : Scheme.{u}} {f : X ⟶ S}
    (α : f.FiberCycleFamily 0) : X → ℤ :=
  fun x ↦
    CycleGroup.toAlgebraicCycle (f.fiberRelativeDimensionFunction (f x)) 0 (α (f x))
        (f.asFiber x) *
      (Field.finInsepDegree (S.residueField (f x)) (X.residueField x) : ℤ)

/-- The value of the function attached to a fibrewise zero-cycle family is its
fibrewise coefficient multiplied by the finite inseparable residue-field degree. -/
theorem weighting_apply {X S : Scheme.{u}} {f : X ⟶ S}
    (α : f.FiberCycleFamily 0) (x : X) :
    weighting α x =
      CycleGroup.toAlgebraicCycle (f.fiberRelativeDimensionFunction (f x)) 0 (α (f x))
          (f.asFiber x) *
        (Field.finInsepDegree (S.residueField (f x)) (X.residueField x) : ℤ) := sorry

/-- A relative zero-cycle on a locally quasi-finite, locally finite type morphism
over a locally Noetherian base determines a weighting. -/
theorem isWeighting_weighting {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (α : f.FiberCycleFamily 0) (hα : IsRelative α) :
    f.IsWeighting (weighting α) := sorry

/-- On a quasi-compact source of a locally quasi-finite, locally finite type
morphism over a locally Noetherian base, every weighting has a positive natural
multiple equal to the weighting attached to a relative zero-cycle. -/
theorem exists_nsmul_eq_weighting {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] (w : X → ℤ) (hw : f.IsWeighting w) :
    ∃ n : ℕ, 0 < n ∧ ∃ α : f.FiberCycleFamily 0,
      IsRelative α ∧ n • w = weighting α := sorry

/-- On a quasi-compact source of a locally quasi-finite, locally finite type
morphism over a locally Noetherian base of prime characteristic `p`, every
weighting has a `p`-power multiple attached to a relative zero-cycle. -/
theorem exists_pow_nsmul_eq_weighting {X S : Scheme.{u}} {f : X ⟶ S}
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] {p : ℕ} [Fact p.Prime] [S.IsCharP p]
    (w : X → ℤ) (hw : f.IsWeighting w) :
    ∃ k : ℕ, ∃ α : f.FiberCycleFamily 0,
      IsRelative α ∧ p ^ k • w = weighting α := sorry

end AlgebraicGeometry.RelativeCycle
