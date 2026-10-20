/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale

/-!
# Basic functors for the etale site

This module exposes the canonical source-scheme functor from the small etale
site.  Affine restrictions of the big and small etale sites live in sibling
modules.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The functor from the small etale site of `S` to schemes which forgets the
etale structure and the morphism to `S`. -/
abbrev smallEtaleToScheme (S : Scheme.{u}) : S.Etale ⥤ Scheme :=
  MorphismProperty.Over.forget @Etale ⊤ S ⋙ Over.forget S

/-- The source-scheme functor from the small etale site preserves pullbacks. -/
theorem smallEtaleToScheme_preservesPullbacks_spec (S : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (smallEtaleToScheme S) := sorry

/-- Typeclass access to pullback preservation by the small etale source functor. -/
instance smallEtaleToScheme_preservesPullbacks (S : Scheme.{u}) :
    PreservesLimitsOfShape WalkingCospan (smallEtaleToScheme S) :=
  smallEtaleToScheme_preservesPullbacks_spec S

end AlgebraicGeometry.Scheme
