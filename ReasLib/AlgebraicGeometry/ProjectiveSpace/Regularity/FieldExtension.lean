/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Regularity
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Twist.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.BaseChange
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# Projective-space regularity after a field extension

This file expresses regularity on the canonical field-extension base change using the pullbacks
of the canonical twists on projective space.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.ProjectiveSpace

namespace FieldExtension

/-- A module sheaf is `m`-regular after extending the ground field when the cohomology of the
field-extension pullback of every required canonical twist vanishes. -/
abbrev IsMRegular
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (n : ℕ) (ℱ : (scheme k n).Modules) (m : ℤ) : Prop :=
  ∀ i : ℕ, 0 < i → i ≤ n →
    IsZero
      (RingedSpace.moduleCohomology
        (Scheme.Modules.FieldExtension.baseChange k k' (toSpec k n)
          (twist k n ℱ (m - i))) i)

end FieldExtension

/-- Regularity with respect to the canonical twists on projective space is preserved and
reflected by every extension of the ground field. -/
theorem isMRegular_iff_fieldExtension
    (k k' : Type u) [Field k] [Field k'] [Algebra k k']
    (n : ℕ) (ℱ : (scheme k n).Modules) [ℱ.IsCoherent] (m : ℤ) :
    IsMRegular k n ℱ m ↔ FieldExtension.IsMRegular k k' n ℱ m := sorry

end AlgebraicGeometry.ProjectiveSpace
