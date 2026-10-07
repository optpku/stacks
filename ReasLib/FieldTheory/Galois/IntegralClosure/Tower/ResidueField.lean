module

public import ReasLib.FieldTheory.Galois.IntegralClosure.Tower
public import ReasLib.RingTheory.Invariant.ResidueField

@[expose] public section

/-!
# Residue fields in towers of Galois integral closures

This file packages the residue-field map induced by an integral-closure tower and its
compatibility with Galois restriction.  The pair-dependent residue-field algebra structures stay
scoped in theorem results.

@stack 0BU7
-/

open scoped Pointwise

universe u v w z

namespace integralClosure.Tower

section Map

variable {A : Type u} {K : Type v} {L : Type w} {M : Type z}
variable [CommRing A] [Field K] [Algebra A K]
variable [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [Normal K L]
variable [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [IsScalarTower K L M] [IsScalarTower A K M] [IsScalarTower A L M]

/-- The integral-closure tower map intertwines the upper Galois action with restriction to the
lower field. -/
@[stacks 0BU7 "Galois equivariance of the integral-closure tower map"]
theorem towerMap_smul (sigma : Gal(M/K)) (x : integralClosure A L) :
    sigma • towerMap (A := A) (L := L) (M := M) x =
      towerMap (A := A) (L := L) (M := M)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L sigma • x) := sorry

end Map

section Contraction

variable {A : Type u} {L : Type v} {M : Type w}
variable [CommRing A] [Field L] [Algebra A L]
variable [Field M] [Algebra L M] [Algebra A M] [IsScalarTower A L M]

/-- The contraction of a prime ideal along an integral-closure tower is prime. -/
@[stacks 0BU7 "prime contraction in an integral-closure tower"]
instance under_isPrime (r : Ideal (integralClosure A M)) [r.IsPrime] :
    (under (A := A) (L := L) (M := M) r).IsPrime := sorry

/-- The contraction of a maximal ideal along an integral-closure tower is maximal. -/
@[stacks 0BU7 "maximal contraction in an integral-closure tower"]
instance under_isMaximal (r : Ideal (integralClosure A M)) [r.IsMaximal] :
    (under (A := A) (L := L) (M := M) r).IsMaximal := sorry

/-- Lying over the base ideal is preserved by contraction through an integral-closure tower. -/
@[stacks 0BU7 "lying over in an integral-closure tower"]
instance under_liesOver (p : Ideal A) (r : Ideal (integralClosure A M))
    [p.IsPrime] [r.IsPrime] [r.LiesOver p] :
    (under (A := A) (L := L) (M := M) r).LiesOver p := sorry

/-- The canonical map from the residue field of a contracted prime to the upper residue field. -/
@[stacks 0BU7 "residue-field map in an integral-closure tower"]
noncomputable def residueMap (r : Ideal (integralClosure A M)) [r.IsPrime] :
    (under (A := A) (L := L) (M := M) r).ResidueField →+* r.ResidueField :=
  Ideal.ResidueField.map
    (under (A := A) (L := L) (M := M) r) r
    (towerMap (A := A) (L := L) (M := M)).toRingHom rfl

/-- On an integral element, the residue-field tower map is induced by `towerMap`. -/
@[simp, stacks 0BU7 "residue-field tower map formula"]
theorem residueMap_algebraMap (r : Ideal (integralClosure A M)) [r.IsPrime]
    (x : integralClosure A L) :
    residueMap (A := A) (L := L) (M := M) r
        (algebraMap (integralClosure A L)
          (under (A := A) (L := L) (M := M) r).ResidueField x) =
      algebraMap (integralClosure A M) r.ResidueField
        (towerMap (A := A) (L := L) (M := M) x) := sorry

end Contraction

section Action

variable {A : Type u} {K : Type v} {L : Type w} {M : Type z}
variable [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra K L] [Algebra A L] [IsScalarTower A K L] [IsGalois K L]
variable [Field M] [Algebra L M] [Algebra K M] [Algebra A M]
  [IsScalarTower K L M] [IsScalarTower A K M] [IsScalarTower A L M] [IsGalois K M]

/-- The residue-field map commutes pointwise with the decomposition-group action and Galois
restriction. -/
@[stacks 0BU7 "naturality of the residue action in a Galois tower"]
theorem decompositionHom_residueMap_apply
    (p : Ideal A) [p.IsPrime]
    (r : Ideal (integralClosure A M)) [r.IsPrime] [r.LiesOver p]
    (sigma : MulAction.stabilizer Gal(M/K) r)
    (x : (under (A := A) (L := L) (M := M) r).ResidueField) :
    -- Local instance justification (defeq pin): select the lower contracted residue algebra in the action square.
    letI : Algebra p.ResidueField
        (under (A := A) (L := L) (M := M) r).ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p
        (under (A := A) (L := L) (M := M) r)
    -- Local instance justification (defeq pin): select the upper residue algebra in the same action square.
    letI : Algebra p.ResidueField r.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p r
    residueMap (A := A) (L := L) (M := M) r
        (Ideal.ResidueField.Invariant.stabilizerHom Gal(L/K) p
          (under (A := A) (L := L) (M := M) r)
          (decompositionHom (A := A) (K := K) (L := L) (M := M) r sigma) x) =
      Ideal.ResidueField.Invariant.stabilizerHom Gal(M/K) p r sigma
        (residueMap (A := A) (L := L) (M := M) r x) := sorry

/-- As ring homomorphisms, the residue-field action square commutes with Galois restriction. -/
@[stacks 0BU7 "commutative residue-action square in a Galois tower"]
theorem decompositionHom_residueMap
    (p : Ideal A) [p.IsPrime]
    (r : Ideal (integralClosure A M)) [r.IsPrime] [r.LiesOver p]
    (sigma : MulAction.stabilizer Gal(M/K) r) :
    -- Local instance justification (defeq pin): select the lower contracted residue algebra for the homomorphism square.
    letI : Algebra p.ResidueField
        (under (A := A) (L := L) (M := M) r).ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p
        (under (A := A) (L := L) (M := M) r)
    -- Local instance justification (defeq pin): select the upper residue algebra for the homomorphism square.
    letI : Algebra p.ResidueField r.ResidueField :=
      Ideal.ResidueField.algebraOfLiesOver p r
    (residueMap (A := A) (L := L) (M := M) r).comp
        (Ideal.ResidueField.Invariant.stabilizerHom Gal(L/K) p
          (under (A := A) (L := L) (M := M) r)
          (decompositionHom (A := A) (K := K) (L := L) (M := M) r sigma)).toRingEquiv.toRingHom =
      (Ideal.ResidueField.Invariant.stabilizerHom Gal(M/K) p r sigma).toRingEquiv.toRingHom.comp
        (residueMap (A := A) (L := L) (M := M) r) := sorry

end Action

end integralClosure.Tower
