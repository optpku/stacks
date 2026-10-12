/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.RingTheory.Completion.LocalRing
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap72.Definition_72_8_1_Modification
public import stacks_project.Chap89.«89_2_0_1_Punctured»

/-!
# Modifications of complete 2-dimensional local domains

A modification of the spectrum of a complete Noetherian local domain of
dimension 2 is a scheme H-projective over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 89.2.4 If `(A, 𝔪, κ)` is a complete Noetherian local domain of
dimension `2`, then every modification of `Spec(A)` is projective over `A`. -/
@[stacks 0AGN]
theorem isScheme_hProjective_of_isModification
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    [IsCompleteLocalRing A] (hdim : ringKrullDim A = 2)
    {X : AlgebraicSpace (Spec (.of A))} [IsIntegral X] [IsIntegral (specSpace A)]
    (f : X ⟶ specSpace A) [IsModification f] :
    ∃ (T : Over (Spec (.of A))), Nonempty (X ≅ ofOver T) ∧ HProjective T.hom :=
  sorry

/-- A modification of `specSpace A` is a scheme when `A` is a complete
Noetherian local domain of dimension `2`. -/
theorem isScheme_of_isModification
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    [IsCompleteLocalRing A] (hdim : ringKrullDim A = 2)
    {X : AlgebraicSpace (Spec (.of A))} [IsIntegral X] [IsIntegral (specSpace A)]
    (f : X ⟶ specSpace A) [IsModification f] :
    IsScheme X :=
  sorry

/-- Any scheme representing a modification of `specSpace A` is H-projective
over `Spec(A)` when `A` is a complete Noetherian local domain of dimension `2`. -/
theorem hProjective_hom_of_isModification
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    [IsCompleteLocalRing A] (hdim : ringKrullDim A = 2)
    {X : AlgebraicSpace (Spec (.of A))} [IsIntegral X] [IsIntegral (specSpace A)]
    (f : X ⟶ specSpace A) [IsModification f]
    {T : Over (Spec (.of A))} (e : X ≅ ofOver T) :
    HProjective T.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
