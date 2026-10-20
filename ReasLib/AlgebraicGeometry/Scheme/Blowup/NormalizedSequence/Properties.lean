/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Normalized.Properties
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.NormalizedSequence
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Modification
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Basic

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.NormalizedBlowupSequence

/-- A finite sequence of normalized blowups of a normal Nagata scheme has normal terminal scheme. -/
theorem terminal_isNormal {X Y : Scheme.{u}} [Scheme.Nagata X]
    (s : Scheme.NormalizedBlowupSequence X Y) (hX : X.isNormal) : Y.isNormal := sorry

/-- A positive-dimensional finite sequence of normalized blowups of an integral Nagata scheme is
a modification of its initial scheme. -/
theorem toSource_isModification {X Y : Scheme.{u}} [Scheme.Nagata X] [IsIntegral X]
    (s : Scheme.NormalizedBlowupSequence X Y) (h_dim : 0 < topologicalKrullDim X) :
    IsModification s.toSource := sorry

/-- A finite sequence of normalized blowups over a Nagata ring admits a closed immersion into
standard projective space whose structure morphism is its composite to the affine base. -/
theorem exists_projectiveSpaceEmbedding {A : Type u} [CommRing A] [NagataRing A]
    {X : Scheme.{u}} (s : Scheme.NormalizedBlowupSequence (Spec (.of A)) X) :
    ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace.scheme A n),
      And (IsClosedImmersion i) ((i ≫ ProjectiveSpace.toSpec A n) = s.toSource) := sorry

end AlgebraicGeometry.Scheme.NormalizedBlowupSequence
