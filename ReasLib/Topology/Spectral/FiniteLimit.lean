/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.TopCat.Limits.Basic
public import Mathlib.Topology.Spectral.Basic
public import ReasLib.Topology.Sober.Finite

/-!
# Directed Limits of Finite `T₀` Spaces

This module owns the finite-stage spectrality theorem used for inverse-system
presentations of spectral spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace TopCat

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]

/-- Lemma 5.23.12: a directed inverse limit of finite `T₀` topological spaces
is spectral. -/
@[stacks 09XV]
theorem spectralSpace_limit_of_directed_finite_t0
    {F : Iᵒᵖ ⥤ TopCat.{u}} [∀ i : Iᵒᵖ, T0Space (F.obj i)]
    [∀ i : Iᵒᵖ, Finite (F.obj i)] :
    SpectralSpace (limit F : TopCat) := sorry

end TopCat
