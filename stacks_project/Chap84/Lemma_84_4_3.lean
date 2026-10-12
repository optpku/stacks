/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Henselian
public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap84.Lemma_84_4_2_Sections

/-!
# Lemma 84.4.3

For a proper algebraic space over a henselian local ring, restriction
identifies global sections of any sheaf of sets on the small étale site
with those of its inverse image on the closed fibre.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 84.4.3: if `A` is a henselian local ring and `X` is an algebraic space
over `Spec A` whose structure morphism is proper, then for the inclusion of the
fibre `X₀` of `toBase X` over the closed point (equivalently the special fibre
at `I = IsLocalRing.maximalIdeal A`), restriction identifies `Γ(X, F)` with
`Γ(X₀, F|_{X₀})` for every sheaf of sets `F` on `X_étale`. -/
@[stacks 0DFZ]
theorem smallEtaleGlobalSections_bijective_of_properHenselianLocal
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))} [Proper (toBase X)]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Function.Bijective
      (smallEtaleGlobalSectionsPullback
        (pullback.fst (toBase X) (ofOverSpecQuotientι (IsLocalRing.maximalIdeal A)))
        F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
