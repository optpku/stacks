/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Reduced
public import stacks_project.Chap62.Lemma_62_6_6_Relative
public import stacks_project.Chap62.Lemma_62_7_3_Equidimensional
public import stacks_project.Chap62.Lemma_62_7_3_Operations

/-!
# Zariski locality of equidimensional fibre cycle families

This file records the source-only and target-only locality companions for
equidimensionality of relative `r`-cycles, together with the closure
characterization used in Stacks Lemma 62.7.4.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
open Scheme.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- The reduced induced structure on the closure of the support of a family of
`r`-cycles on fibres. -/
noncomputable abbrev reducedSupportClosure {X S : Scheme.{u}} {f : X ⟶ S}
    {r : ℕ} (α : Family f r) :
    Scheme.ClosedSubschemeStructure (TopologicalSpace.Closeds.closure (support α)) :=
  Scheme.ClosedSubschemeStructure.reduced
    (TopologicalSpace.Closeds.closure (support α))

/-- Equidimensionality of a family of `r`-cycles on fibres is equivalent to the
reduced induced closed subscheme on the closure of its support having relative
dimension at most `r` over `S`. -/
theorem equidimensional_iff_closure {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (α : Family f r) :
    Equidimensional α ↔
      RelativeDimensionLE ((reducedSupportClosure α).ι ≫ f) r := sorry

/-- Equidimensionality is equivalent to local finite type of the reduced
induced structure morphism on the closure of the support, together with a
pointwise relative-dimension bound of at most `r` at the points of that
closure. -/
theorem equidimensional_iff_closure_at {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (α : Family f r) :
    Equidimensional α ↔
      LocallyOfFiniteType ((reducedSupportClosure α).ι ≫ f) ∧
        ∀ x, RelativeDimensionLEAt ((reducedSupportClosure α).ι ≫ f) r x :=
  sorry

/-- The support of a restriction to compatible opens `U ⊆ X` and `V ⊆ S` is the
preimage of `support α ∩ U` along `U.ι`. -/
theorem support_restrict {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α : Family f r) (U : X.Opens) (V : S.Opens) (hUV : U ≤ f ⁻¹ᵁ V) :
    U.ι '' support (restrict α U V hUV) = support α ∩ U := sorry

/-- Equidimensionality of a relative `r`-cycle may be checked after restriction
to the members of an open cover of the source. -/
theorem equidimensional_iff_of_source_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : Family f r) (hα : IsRelative α) {ι : Type u}
    (U : ι → X.Opens) (hU : iSup U = ⊤) :
    Equidimensional α ↔
      ∀ i, Equidimensional (restrict α (U i) ⊤ le_top) := sorry

/-- Equidimensionality of a relative `r`-cycle may be checked after restriction
to the preimages of the members of an open cover of the target. -/
theorem equidimensional_iff_of_target_iSup_eq_top
    {X S : Scheme.{u}} [IsLocallyNoetherian S] {f : X ⟶ S} [LocallyOfFiniteType f]
    {r : ℕ} (α : Family f r) (hα : IsRelative α) {κ : Type u}
    (V : κ → S.Opens) (hV : iSup V = ⊤) :
    Equidimensional α ↔
      ∀ j, Equidimensional (restrict α (f ⁻¹ᵁ V j) (V j) le_rfl) := sorry

end AlgebraicGeometry.RelativeCycle
