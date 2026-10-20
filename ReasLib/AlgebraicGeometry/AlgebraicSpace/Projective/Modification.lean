/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Modification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PuncturedSpectrum

/-!
# Projectivity of modifications over complete local surfaces

Every modification of the spectrum of a complete Noetherian local domain of
Krull dimension two is represented by an H-projective scheme over the base.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A modification of the spectrum of a complete Noetherian local domain of
Krull dimension two is represented by an H-projective scheme over the base. -/
@[stacks 0AGN]
theorem isScheme_hProjective_of_isModification
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsDomain A]
    [IsCompleteLocalRing A] (hdim : ringKrullDim A = 2)
    {X : AlgebraicSpace (Spec (.of A))} [IsIntegral X] [IsIntegral (specSpace A)]
    (f : X ⟶ specSpace A) [IsModification f] :
    ∃ (T : Over (Spec (.of A))), Nonempty (X ≅ ofOver T) ∧ HProjective T.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
