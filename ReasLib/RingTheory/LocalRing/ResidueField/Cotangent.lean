/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Extension.ExtendScalars
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cotangent space of a residue-field presentation

@stack 0DYH

This leaf owns the concrete surjective presentation of a residue field and the
canonical cotangent and first-cotangent-homology identifications attached to it.
The Jacobi--Zariski maps and the zero-ended exact row live in companion leaves.
-/

@[expose] public section

open Algebra
open IsLocalRing

universe v

namespace IsLocalRing.ResidueField

noncomputable section

variable (B : Type v) [CommRing B] [IsLocalRing B]

/- The chosen section is kept transparent so the canonical `B` instances remain inferable. -/
/-- A surjective presentation of the residue field whose underlying ring is `B`. -/
@[stacks 0DYH "residue-field presentation"]
noncomputable abbrev presentation : Extension B (ResidueField B) where
  Ring := B
  algebra₂ := inferInstance
  isScalarTower := inferInstance
  σ := Function.surjInv <|
    (IsLocalRing.ResidueField.algebraMap_eq B).symm ▸ IsLocalRing.residue_surjective
  algebraMap_σ := Function.rightInverse_surjInv <|
    (IsLocalRing.ResidueField.algebraMap_eq B).symm ▸ IsLocalRing.residue_surjective

/-- The kernel of the residue-field presentation is the maximal ideal. -/
@[simp, stacks 0DYH "residue presentation kernel"]
theorem presentation_ker : (presentation B).ker = maximalIdeal B := sorry

/- The B-linear version is useful before extending scalars to the residue field. -/
/-- The cotangent module of the maximal ideal identified with the cotangent module of the
kernel of the residue quotient. -/
@[stacks 0DYH "residue presentation kernel cotangent identification"]
noncomputable def kerCotangentEquiv :
    (maximalIdeal B).Cotangent ≃ₗ[B]
      (RingHom.ker (algebraMap B (ResidueField B))).Cotangent :=
  Ideal.Cotangent.equivOfEq _ _
    ((congrArg RingHom.ker (IsLocalRing.ResidueField.algebraMap_eq B)).trans
      IsLocalRing.ker_residue).symm

/- The equivalence below uses the canonical kernel computation directly, so its concrete data
does not depend on the deferred proof of `presentation_ker`. -/

/-- The presentation cotangent module identified with the cotangent space of `B`. -/
@[stacks 0DYH "residue-field cotangent identification"]
noncomputable def cotangentEquiv :
    (presentation B).Cotangent ≃ₗ[ResidueField B] CotangentSpace B :=
  ((presentation B).cotangentEquivCotangentKer.trans
    (Ideal.Cotangent.equivOfEq _ _
      ((congrArg RingHom.ker (IsLocalRing.ResidueField.algebraMap_eq B)).trans
        IsLocalRing.ker_residue))).extendScalarsOfSurjective
      ((IsLocalRing.ResidueField.algebraMap_eq B).symm ▸ IsLocalRing.residue_surjective)

/-- The canonical identification
`Algebra.H1Cotangent B (ResidueField B) ≃ₗ[ResidueField B] CotangentSpace B`. -/
@[stacks 0DYH "residue-field H₁/cotangent identification"]
noncomputable def h1CotangentEquiv :
    Algebra.H1Cotangent B (ResidueField B) ≃ₗ[ResidueField B] CotangentSpace B :=
  (presentation B).h1CotangentEquivCotangent.trans (cotangentEquiv B)

end

end IsLocalRing.ResidueField
