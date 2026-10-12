/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Sheaf.Subset
public import ReasLib.Topology.Sheaf.InverseLimit.FinitePresentation
import Mathlib.Tactic.CrossRefAttribute

/-!
# Constructible embeddings of finitely presented sheaves

This file turns a finite compact-open presentation on a spectral space into a finite
constructible stratification target. The presentation hypothesis is the generic
finite-coequalizer property, so downstream users do not depend on a particular choice of
lower-shriek generators.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Topology
open scoped TopCat

noncomputable section

universe u

namespace TopCat.Sheaf.CompactOpenPresentation

variable {X : TopCat.{u}}
variable [HasWeakSheafify (Opens.grothendieckTopology X) (Type u)]

/-- Lemma 17.19.4 (0CAL): a finitely compact-open-presented set-valued sheaf on a spectral
space embeds into a finite product of pushforwards of finite constant sheaves from constructible
closed subsets. -/
@[stacks 0CAL]
theorem IsFinite.existsConstructibleEmbedding [SpectralSpace X]
    {F : X.Sheaf (Type u)} (hF : IsFinite F) :
    ∃ (n : ℕ) (Z : Fin n → Closeds X)
      (_ : ∀ a, IsConstructible (Z a : Set X))
      (A : Fin n → Type u) (_ : ∀ a, Finite (A a)),
      ∃ φ : F ⟶
        ∏ᶜ fun a : Fin n ↦
          (Sheaf.pushforward (Type u)
            (TopCat.subsetInclusion (Z a : Set X))).obj
              ((constantSheaf
                (Opens.grothendieckTopology (TopCat.of (Z a : Set X)))
                (Type u)).obj (A a)),
        Mono φ := sorry

end TopCat.Sheaf.CompactOpenPresentation
