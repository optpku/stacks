/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap84.Lemma_84_4_1_Equalizer

/-!
# Lemma 84.4.1

For a surjective proper morphism of algebraic spaces, the small étale unit of a
sheaf of sets is the equalizer of the two maps induced by the projections of
the fibre product.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : Y ⟶ X)
variable (F : Sheaf (smallEtaleTopology X) (Type (u + 1)))

/-- Lemma 84.4.1: let `S` be a scheme, let `f : Y ⟶ X` be a surjective proper
morphism of algebraic spaces over `S`, and let `F` be a sheaf of sets on
`X_étale`. Then the unit `F ⟶ f_* f⁻¹ F` is injective, with image the equalizer
of the two maps `f_* f⁻¹ F ⇉ g_* g⁻¹ F` induced by the projections of
`g : Y ×_X Y ⟶ X`. -/
@[stacks 0DFX]
theorem smallEtaleUnit_isEqualizer [Proper f] [Surjective f] :
    IsEqualizer (smallEtaleUnit f F) (smallEtaleFstMap f F) (smallEtaleSndMap f F)
      (smallEtaleUnit_equalizes f F) :=
  sorry

/-- The unit `F ⟶ f_* f⁻¹ F` is a monomorphism for a surjective proper morphism
of algebraic spaces. -/
theorem smallEtaleUnit_mono [Proper f] [Surjective f] :
    Mono (smallEtaleUnit f F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
