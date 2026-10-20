/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Affine étale atlases of quasi-compact algebraic spaces

An algebraic space is quasi-compact if and only if it admits a representable étale
locally-surjective atlas from an affine scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space is quasi-compact if and only if it admits a representable étale
locally-surjective atlas from an affine scheme. -/
theorem isQuasiCompact_iff_exists_affineEtale {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsQuasiCompact X ↔
      ∃ (U : Over S) (f : ofOver U ⟶ X),
        (MorphismProperty.over (@Etale)).presheaf f ∧
          Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
            IsAffine U.left :=
  sorry

/-- A representable étale locally-surjective atlas from an affine scheme witnesses that the
algebraic space is quasi-compact. -/
theorem isQuasiCompact_of_affineEtale {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (f : ofOver U ⟶ X) (h_etale : (MorphismProperty.over (@Etale)).presheaf f)
    (h_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f)
    [IsAffine U.left] : IsQuasiCompact X :=
  (isQuasiCompact_iff_exists_affineEtale X).mpr ⟨U, f, h_etale, h_surj, inferInstance⟩

/-- A quasi-compact algebraic space admits a representable étale locally-surjective atlas from an
affine scheme. -/
theorem exists_affineEtale_of_isQuasiCompact {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] :
    ∃ (U : Over S) (f : ofOver U ⟶ X),
      (MorphismProperty.over (@Etale)).presheaf f ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) f ∧
          IsAffine U.left :=
  (isQuasiCompact_iff_exists_affineEtale X).mp inferInstance

end AlgebraicGeometry.AlgebraicSpace
