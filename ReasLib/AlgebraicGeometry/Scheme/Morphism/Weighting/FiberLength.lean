/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.SeparableClosure
public import Mathlib.RingTheory.Length
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Weighting

/-!
# Fibre-length weightings

This module defines the pointwise weight obtained from the length of a local
closed fibre and the inseparable degree of the corresponding residue-field
extension.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The fibre weight at `x` is the length of the local closed fibre at `x`, multiplied by
the finite inseparable degree of `κ(x)` over `κ(f x)`. -/
noncomputable def fiberWeight {X Y : Scheme.{u}} (f : X ⟶ Y) : X → ℤ :=
  fun x ↦
    ((Module.length (X.presheaf.stalk x)
          ((X.presheaf.stalk x) ⧸
            (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat *
        Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) : ℕ)

/-- The value of `fiberWeight` is the local closed-fibre length times the finite
inseparable residue-field degree. -/
theorem fiberWeight_apply {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) :
    f.fiberWeight x =
      ((Module.length (X.presheaf.stalk x)
            ((X.presheaf.stalk x) ⧸
              (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map (f.stalkMap x).hom)).toNat *
          Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) : ℕ) := sorry

/-- For a locally quasi-finite, locally finitely presented, flat morphism, the fibre weight
is a weighting and is strictly positive at every point. -/
@[stacks 0F3D]
theorem fiberWeight_isPositiveWeighting {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] [LocallyOfFinitePresentation f] [Flat f] :
    f.IsWeighting f.fiberWeight ∧ ∀ x : X, 0 < f.fiberWeight x := sorry

end AlgebraicGeometry.Scheme.Hom
