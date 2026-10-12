/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Maps Between Canonical Truncations

This leaf owns the canonical comparison maps between two canonical truncations
of one cochain complex.  The maps are indexed by an arbitrary inequality, not
only adjacent degrees, so truncation towers and filtration arguments can share
the same construction.
-/

open CategoryTheory

noncomputable section

universe u v

namespace CochainComplex

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]

/-- Stacks 06XX: the canonical map from `K.truncLE a` to `K.truncLE b` induced by
an inequality `a ≤ b`. -/
@[stacks 06XX]
noncomputable def truncLEMapOfLE (K : CochainComplex 𝒜 ℤ) {a b : ℤ} (hab : a ≤ b) :
    K.truncLE a ⟶ K.truncLE b :=
  -- This bound depends on the explicit inequality, so it cannot be a global instance.
  letI : (K.truncLE a).IsStrictlyLE b :=
    (K.truncLE a).isStrictlyLE_of_le a b hab
  inv ((K.truncLE a).ιTruncLE b) ≫ CochainComplex.truncLEMap (K.ιTruncLE a) b

/-- The canonical upper-truncation transition followed by the target inclusion is the source
inclusion. -/
@[stacks 06XX]
theorem truncLEMapOfLE_comp_ιTruncLE (K : CochainComplex 𝒜 ℤ) {a b : ℤ} (hab : a ≤ b) :
    truncLEMapOfLE K hab ≫ K.ιTruncLE b = K.ιTruncLE a := sorry

/-- Stacks 070F: the canonical map from `K.truncGE a` to `K.truncGE b` induced by
an inequality `a ≤ b`. -/
@[stacks 070F]
noncomputable def truncGEMapOfLE (K : CochainComplex 𝒜 ℤ) {a b : ℤ} (hab : a ≤ b) :
    K.truncGE a ⟶ K.truncGE b :=
  -- This bound depends on the explicit inequality, so it cannot be a global instance.
  letI : (K.truncGE b).IsStrictlyGE a :=
    (K.truncGE b).isStrictlyGE_of_ge a b hab
  CochainComplex.truncGEMap (K.πTruncGE b) a ≫ inv ((K.truncGE b).πTruncGE a)

/-- Precomposing the lower-truncation transition with the source projection gives the target
projection. -/
@[stacks 070F]
theorem πTruncGE_comp_truncGEMapOfLE (K : CochainComplex 𝒜 ℤ) {a b : ℤ} (hab : a ≤ b) :
    K.πTruncGE a ≫ truncGEMapOfLE K hab = K.πTruncGE b := sorry

end CochainComplex
