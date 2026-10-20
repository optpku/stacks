/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Veronese.Internal
public import ReasLib.Algebra.Module.Graded.Veronese

@[expose] public section

open scoped DirectSum

universe u

section Ring

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/- Lemma 27.11.8: the Veronese ring retains its internal homogeneous pieces,
explicit inclusion, and coordinate decomposition. -/
#check (GradedRing.Veronese.grading 𝒜 :
  ∀ d : ℕ, ℕ → Submodule ℤ (GradedRing.Veronese 𝒜 d))
#check (GradedRing.Veronese.inclusion 𝒜 : ∀ d : ℕ, GradedRing.Veronese 𝒜 d →+* A)
#check (GradedRing.Veronese.decomposition 𝒜 :
  ∀ d : ℕ, DirectSum.Decomposition (GradedRing.Veronese.grading 𝒜 d))

end Ring

section Module

variable {M τ : Type u} [AddCommGroup M] [SetLike τ M] [AddSubgroupClass τ M]
  (ℳ : ℤ → τ) [DirectSum.Decomposition ℳ]

/- Lemma 27.11.8: the selected module direct sum retains its internal grading
and explicit coordinate decomposition. -/
#check (GradedModule.Veronese.grading ℳ :
  ∀ d : ℕ, ℤ → Submodule ℤ (GradedModule.Veronese ℳ d))
#check (GradedModule.Veronese.decomposition ℳ :
  ∀ d : ℕ, DirectSum.Decomposition (GradedModule.Veronese.grading ℳ d))

end Module
