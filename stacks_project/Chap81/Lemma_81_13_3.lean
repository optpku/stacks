module

public import stacks_project.Chap81.Lemma_81_13_3_Glueing

/-!
# Lemma 81.13.3

In Situation 81.13.2, the kernel-pair coequalizer of `Y = X' ⨿ Z → X` exists
in algebraic spaces over `S`. The structure morphism `X₁ ⟶ X` is a finite
universal homeomorphism, an isomorphism over the complementary open `U`, and
the closed immersion `Z ⟶ X` lifts through `X₁`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

variable {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}

/-- Lemma 81.13.3 (1): in Situation 81.13.2, let `Y = closedCoprod f i` be
`X' ⨿ Z` and let `R` be the kernel pair of `g = closedCoprodToAmbient f i`,
with projections `t = fst g` and `s = snd g`. Then `fromClosedCoprod f i` is a
coequalizer of `s, t` in `AlgebraicSpace S`. -/
@[stacks 0AGI]
theorem isCoequalizer (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] {W : AlgebraicSpace S}
    (φ : closedCoprod f i ⟶ W)
    (h_equalizes : fst (closedCoprodToAmbient f i) ≫ φ =
      snd (closedCoprodToAmbient f i) ≫ φ) :
    ∃! ψ : closedSpace f i ⟶ W, fromClosedCoprod f i ≫ ψ = φ :=
  sorry

/-- Lemma 81.13.3 (2): the structure morphism `closedSpaceToAmbient f i : X₁ ⟶ X`
is finite. -/
@[stacks 0AGI, instance]
instance instIsFinite_closedSpaceToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsLocallyNoetherian X] [IsClosedImmersion i] [Proper f] :
    IsFinite (closedSpaceToAmbient f i) :=
  inferInstance

/-- Lemma 81.13.3 (3): the structure morphism `closedSpaceToAmbient f i : X₁ ⟶ X`
is a universal homeomorphism. -/
@[stacks 0AGI]
theorem universalHomeomorphism_closedSpaceToAmbient (f : X' ⟶ X)
    (i : Z ⟶ X) [IsLocallyNoetherian X] [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    UniversalHomeomorphism (closedSpaceToAmbient f i) :=
  sorry

/-- Lemma 81.13.3 (4): the structure morphism `closedSpaceToAmbient f i : X₁ ⟶ X`
is an isomorphism over the complementary open `U` of `i`. -/
@[stacks 0AGI]
theorem isIsoOverOpen_closedSpaceToAmbient (f : X' ⟶ X) (i : Z ⟶ X)
    [IsLocallyNoetherian X] [IsClosedImmersion i] [Proper f]
    (h_iso : IsIsoOverOpen f (closedImmersionComplementι i)) :
    IsIsoOverOpen (closedSpaceToAmbient f i) (closedImmersionComplementι i) :=
  sorry

/-- Lemma 81.13.3 (5): the closed immersion `i : Z ⟶ X` lifts through `X₁` via
`closedLift`. -/
@[stacks 0AGI]
theorem closedLift_comp (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
    [IsClosedImmersion i] [Proper f] :
    closedLift f i ≫ closedSpaceToAmbient f i = i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing
