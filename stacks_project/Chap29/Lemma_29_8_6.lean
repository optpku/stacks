/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiCompact.GenericPointAvoidance
import StacksCheckRecall

/-!
# Lemma 29.8.6

A quasi-compact morphism misses an open neighbourhood of any irreducible-component generic point
that is not in its image.

@stack 02NE
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

/- Lemma 29.8.6
A quasi-compact morphism misses an open neighbourhood of any irreducible-component generic point
that is not in its image.
-/
@[stacks 02NE] #check
  (AlgebraicGeometry.exists_open_preimage_eq_bot_of_genericPoint_not_mem_range :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] {η : S}
        {Z : irreducibleComponents S},
      IsGenericPoint η (Z : Set S) → η ∉ Set.range f.base →
        ∃ V : S.Opens, η ∈ V ∧ f ⁻¹ᵁ V = ⊥)
