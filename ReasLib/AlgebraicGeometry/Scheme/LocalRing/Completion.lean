/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.ResidueField.Instances
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Completed local rings of schemes

This leaf provides the canonical reduction map from a completed local ring to
the residue field of the original stalk.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

noncomputable section

/-- Quotienting a local ring by its maximal ideal recovers its residue field. -/
noncomputable abbrev quotientMaximalIdealResidueFieldRingEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    (R ⧸ IsLocalRing.maximalIdeal R) ≃+* IsLocalRing.ResidueField R :=
  (RingEquiv.ofBijective
    (algebraMap (R ⧸ IsLocalRing.maximalIdeal R)
      ((IsLocalRing.maximalIdeal R).ResidueField))
    (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R))).trans
      ((RingEquiv.ofBijective
        (algebraMap (IsLocalRing.ResidueField R)
          ((IsLocalRing.maximalIdeal R).ResidueField))
        (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal R))).symm)

/-- Reducing the completion of the local ring of `X` at `x` modulo its completed
maximal ideal gives the residue field at `x`. -/
noncomputable abbrev completedStalkResidueFieldMap (X : Scheme.{u}) (x : X) :
    AdicCompletion (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+*
      X.residueField x :=
  (quotientMaximalIdealResidueFieldRingEquiv (X.presheaf.stalk x)).toRingHom.comp
    (AdicCompletion.evalOneₐ (IsLocalRing.maximalIdeal (X.presheaf.stalk x))).toRingHom

end

end AlgebraicGeometry.Scheme
