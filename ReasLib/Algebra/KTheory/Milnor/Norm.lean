/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.KTheory.Milnor.Residue
public import ReasLib.RingTheory.Localization.AtPrime.FractionRing
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.DedekindDomain.Dvr

@[expose] public section

noncomputable section

open scoped BigOperators

universe u v w

set_option backward.privateInPublic true

namespace MilnorK

private abbrev NormPrime (k : Type u) [Field k] :=
  {p : Polynomial k // p.Monic ∧ Irreducible p}

private instance primeFact (k : Type u) [Field k] (p : NormPrime k) : Fact (Irreducible p.1) :=
  ⟨p.2.2⟩

private noncomputable abbrev primeIdeal (k : Type u) [Field k] (p : NormPrime k) : Ideal (Polynomial k) :=
  Ideal.span {p.1}

private instance primeIdealPrime (k : Type u) [Field k] (p : NormPrime k) :
    (primeIdeal k p).IsPrime :=
  inferInstanceAs (Ideal.span {p.1}).IsPrime

private instance primeDVR (k : Type u) [Field k] (p : NormPrime k) :
    IsDiscreteValuationRing (Localization.AtPrime (primeIdeal k p)) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (Polynomial k)
    (fun (h : primeIdeal k p = ⊥) ↦ p.2.2.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    (Localization.AtPrime (primeIdeal k p))

private noncomputable def primeEvaluation (k : Type u) [Field k] (p : NormPrime k) :
    Localization.AtPrime (primeIdeal k p) →+* AdjoinRoot p.1 where
  toFun a :=
    let fraction := IsLocalization.sec (primeIdeal k p).primeCompl a
    AdjoinRoot.mk p.1 fraction.1 / AdjoinRoot.mk p.1 fraction.2.1
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

private instance primeEvaluationLocal (k : Type u) [Field k] (p : NormPrime k) :
    IsLocalHom (primeEvaluation k p) := sorry

private noncomputable def primeFractionMap (k : Type u) [Field k] (p : NormPrime k) :
    RatFunc k →+* FractionRing (Localization.AtPrime (primeIdeal k p)) :=
  -- Local instance justification (defeq pin): the fraction-ring comparison fixes this localization algebra in its result type.
  letI : Algebra (Localization.AtPrime (primeIdeal k p)) (RatFunc k) :=
    IsLocalization.localizationAlgebraOfSubmonoidLe
      (Localization.AtPrime (primeIdeal k p)) (RatFunc k)
      (primeIdeal k p).primeCompl (nonZeroDivisors (Polynomial k))
      (primeIdeal k p).primeCompl_le_nonZeroDivisors
  (Localization.AtPrime.fractionRingAlgEquiv (primeIdeal k p) :
    FractionRing (Localization.AtPrime (primeIdeal k p)) ≃ₐ[
      Localization.AtPrime (primeIdeal k p)] RatFunc k).symm.toRingHom

private noncomputable def primeResidue (k : Type u) [Field k] (p : NormPrime k) (i : ℕ) :
    Group (i + 1) (RatFunc k) →+ Group i (AdjoinRoot p.1) :=
  (mapGroup (IsLocalRing.ResidueField.lift (primeEvaluation k p)) i).comp
    ((dvrBoundary (Localization.AtPrime (primeIdeal k p))
      (FractionRing (Localization.AtPrime (primeIdeal k p))) i).comp
        (mapGroup (primeFractionMap k p) (i + 1)))


private noncomputable def zeroPrime (k : Type u) [Field k] : NormPrime k :=
  ⟨Polynomial.X, Polynomial.monic_X, Polynomial.irreducible_X⟩

private noncomputable def zeroEvaluation (k : Type u) [Field k] :
    Localization.AtPrime (primeIdeal k (zeroPrime k)) →+* k where
  toFun a :=
    let fraction := IsLocalization.sec (primeIdeal k (zeroPrime k)).primeCompl a
    fraction.1.eval 0 / fraction.2.1.eval 0
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

private instance zeroEvaluationLocal (k : Type u) [Field k] :
    IsLocalHom (zeroEvaluation k) := sorry

private noncomputable def invertVariable (k : Type u) [Field k] : RatFunc k →+* RatFunc k where
  toFun a :=
    a.num.eval₂ (RatFunc.C : k →+* RatFunc k) (RatFunc.X⁻¹) /
      a.denom.eval₂ (RatFunc.C : k →+* RatFunc k) (RatFunc.X⁻¹)
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

private noncomputable def infinityResidue (k : Type u) [Field k] (i : ℕ) :
    Group (i + 1) (RatFunc k) →+ Group i k :=
  ((mapGroup (IsLocalRing.ResidueField.lift (zeroEvaluation k)) i).comp
    ((dvrBoundary (Localization.AtPrime (primeIdeal k (zeroPrime k)))
      (FractionRing (Localization.AtPrime (primeIdeal k (zeroPrime k)))) i).comp
        (mapGroup (primeFractionMap k (zeroPrime k)) (i + 1)))).comp
      (mapGroup (invertVariable k) (i + 1))

private noncomputable def finiteResidues (k : Type u) [Field k] (i : ℕ)
    (a : Group (i + 1) (RatFunc k)) :
    (p : NormPrime k) → Group i (AdjoinRoot p.1) :=
  fun p ↦ primeResidue k p i a

/-- Every residue class at one finite place has a rational-function lift vanishing at all
other finite places. -/
private theorem finiteResidues_single_mem_range (k : Type u) [Field k]
    (p : NormPrime k) (i : ℕ) (a : Group i (AdjoinRoot p.1)) :
    (@Pi.single _ _ _ (Classical.decEq _) p a) ∈ Set.range (finiteResidues k i) := sorry

/-- The inverse-function choice lifts the specified single-place residue family. -/
private theorem finiteResidues_invFun_single (k : Type u) [Field k]
    (p : NormPrime k) (i : ℕ) (a : Group i (AdjoinRoot p.1)) :
    finiteResidues k i
      (Function.invFun (finiteResidues k i) (@Pi.single _ _ _ (Classical.decEq _) p a)) =
        @Pi.single _ _ _ (Classical.decEq _) p a := sorry

/-- The Bass–Tate norm is the negative infinity residue of a lift with the prescribed
residue at one finite place and zero residues at all other finite places. -/
private noncomputable def simplePolynomialNorm (k : Type u) [Field k]
    (p : NormPrime k) (i : ℕ) : Group i (AdjoinRoot p.1) →+ Group i k where
  toFun a := -infinityResidue k i
    (Function.invFun (finiteResidues k i) (@Pi.single _ _ _ (Classical.decEq _) p a))
  map_zero' := sorry
  map_add' := sorry

/-- Exactness of the rational-function residue sequence makes the norm independent
of the selected lift. -/
private theorem simplePolynomialNorm_spec (k : Type u) [Field k]
    (p : NormPrime k) (i : ℕ) (a : Group i (AdjoinRoot p.1))
    (lift : Group (i + 1) (RatFunc k))
    (hres : finiteResidues k i lift = @Pi.single _ _ _ (Classical.decEq _) p a) :
    simplePolynomialNorm k p i a = -infinityResidue k i lift := sorry

private noncomputable def simpleNormAt (k L : Type u) [Field k] [Field L]
    (p : NormPrime k) (scalarMap : k →+* L) (generator : L)
    (hroot : p.1.eval₂ scalarMap generator = 0) (i : ℕ) (a : Group i L) : Group i k :=
  simplePolynomialNorm k p i
    (Function.invFun (mapGroup (AdjoinRoot.lift scalarMap generator hroot) i) a)

private noncomputable def simpleNormValue (k L : Type u) [Field k] [Field L]
    (scalarMap : k →+* L) (generator : L) (i : ℕ) (a : Group i L) : Group i k :=
  -- Local instance justification (noncanonical choice): this is the specified edge of the generating tower, not an alternative ambient algebra.
  letI : Algebra k L := scalarMap.toAlgebra
  @dite _ ((minpoly k generator).Monic ∧ Irreducible (minpoly k generator))
    (Classical.propDecidable _) (fun hp ↦
      simpleNormAt k L ⟨minpoly k generator, hp⟩ scalarMap generator
        (minpoly.aeval k generator) i a) (fun _ ↦ 0)

private noncomputable def normStage (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Module.Finite k L] (m : ℕ) : IntermediateField k L :=
  IntermediateField.adjoin k
    {a | ∃ r : Fin (Module.finrank k L), r.1 < m ∧ a = Module.finBasis k L r}

private theorem normStage_le (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Module.Finite k L] (m : ℕ) : normStage k L m ≤ normStage k L (m + 1) := sorry

/-- The bottom generating stage induces a bijection on Milnor groups. -/
private theorem normStage_zero_map_bijective (k L : Type u) [Field k] [Field L]
    [Algebra k L] [Module.Finite k L] (i : ℕ) :
    Function.Bijective (mapGroup (algebraMap k (normStage k L 0)) i) := sorry

/-- The full generating stage induces a bijection on Milnor groups. -/
private theorem normStage_top_map_bijective (k L : Type u) [Field k] [Field L]
    [Algebra k L] [Module.Finite k L] (i : ℕ) :
    Function.Bijective (mapGroup (k := normStage k L (Module.finrank k L)) (L := L)
      (normStage k L (Module.finrank k L)).subtype i) := sorry

private noncomputable def normStep (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Module.Finite k L] (i m : ℕ) :
    Group i (normStage k L (m + 1)) →+ Group i (normStage k L m) where
  toFun a := @dite _ (m < Module.finrank k L) (Classical.propDecidable _) (fun hm ↦
    simpleNormValue (normStage k L m) (normStage k L (m + 1))
      (IntermediateField.inclusion (normStage_le k L m)).toRingHom
      ⟨Module.finBasis k L ⟨m, hm⟩, sorry⟩ i a)
    (fun _ ↦ Function.invFun
      (mapGroup (IntermediateField.inclusion (normStage_le k L m)).toRingHom i) a)
  map_zero' := sorry
  map_add' := sorry

private noncomputable def normStages (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Module.Finite k L] (i : ℕ) :
    (m : ℕ) → Group i (normStage k L m) →+ Group i (normStage k L 0)
  | 0 => AddMonoidHom.id _
  | m + 1 => (normStages k L i m).comp (normStep k L i m)

/-- Compose the simple-extension norms along the tower generated by a finite basis.
The inverse functions only identify the bottom and top stages with the given fields. -/
private noncomputable def finiteNorm (k L : Type u) [Field k] [Field L] [Algebra k L]
    [Module.Finite k L] (i : ℕ) : Group i L →+ Group i k where
  toFun a := Function.invFun (mapGroup (algebraMap k (normStage k L 0)) i)
    (normStages k L i (Module.finrank k L)
      (Function.invFun (mapGroup (normStage k L (Module.finrank k L)).subtype i) a))
  map_zero' := sorry
  map_add' := sorry


private instance residueBranchTower (A F : Type u) [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] (b : NormalizationBranch A F) :
    IsScalarTower A (IsLocalRing.maximalIdeal A).ResidueField b.ResidueField := sorry

private instance finiteBranch (A F : Type u) [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] [Module.Finite A (integralClosure A F)]
    (b : NormalizationBranch A F) :
    Module.Finite (IsLocalRing.maximalIdeal A).ResidueField b.ResidueField :=
  -- Local instance justification (proof-local temporary data): restrict the finite-module proof for this particular branch to the closed residue field.
  letI : Module.Finite A b.ResidueField :=
    Module.Finite.trans (integralClosure A F) b.ResidueField
  Module.Finite.of_restrictScalars_finite A (IsLocalRing.maximalIdeal A).ResidueField
    b.ResidueField

/-- The Milnor norm on each finite normalization-residue extension, obtained by the
Bass–Tate construction and composition along a finite generating tower. Its maps do not
depend on a dimension function or on a choice of coniveau degrees. -/
noncomputable def normalizationResidueMilnorNorm
    (A F : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A] [Field F] [Algebra A F] [IsFractionRing A F]
    (b : NormalizationBranch A F) : NormalizationResidueTransfer A F b where
  map i := (mapGroup
    (IsLocalRing.ResidueField.maximalIdealAlgEquiv A).symm.toRingHom i).comp
      (finiteNorm (IsLocalRing.maximalIdeal A).ResidueField b.ResidueField i)
  degreeZero_apply := sorry
  degreeOne_apply := sorry
  projection_formula_symbols := sorry


/-- The normalization-residue Milnor norm has the branch degree as its degree-zero map. -/
theorem normalizationResidueMilnorNorm_zero
    (A F : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A] [Field F] [Algebra A F] [IsFractionRing A F]
    (b : NormalizationBranch A F) (z : ℤ) :
    (normalizationResidueMilnorNorm A F b).map 0 (degreeZeroMap b.ResidueField z) =
      degreeZeroMap (IsLocalRing.ResidueField A)
        ((normalizationResidueDegree A F b : ℤ) * z) :=
  (normalizationResidueMilnorNorm A F b).degreeZero_apply z

/-- The degree-one member is the ordinary norm of the finite branch residue extension. -/
theorem normalizationResidueMilnorNorm_one
    (A F : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A] [Field F] [Algebra A F] [IsFractionRing A F]
    (b : NormalizationBranch A F) (a : Additive b.ResidueFieldˣ) :
    (normalizationResidueMilnorNorm A F b).map 1 (degreeOneMap b.ResidueField a) =
      degreeOneMap (IsLocalRing.ResidueField A) (normalizationResidueNormOne A F b a) :=
  (normalizationResidueMilnorNorm A F b).degreeOne_apply a

/-- For an excellent one-dimensional Noetherian local
domain `A` with fraction field `F`, the normalization-and-norm boundary is the finite sum of
branchwise DVR boundaries composed with the canonical Milnor residue-field norms. -/
noncomputable def canonicalExcellentLocalBoundary
    (A F : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1)
    (i : ℕ) :
    MilnorK.Group (i + 1) F →+
      MilnorK.Group i (IsLocalRing.ResidueField A) :=
  MilnorK.excellentLocalBoundary A F hdim (MilnorK.normalizationResidueMilnorNorm A F) i

/-- The excellent-local boundary is the branch sum of the DVR boundaries followed by the
canonical normalization-residue Milnor norms. -/
theorem canonicalExcellentLocalBoundary_apply
    (A F : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1)
    (i : ℕ) (a : MilnorK.Group (i + 1) F) :
    canonicalExcellentLocalBoundary A F hdim i a =
      ∑ᶠ b, (MilnorK.normalizationResidueMilnorNorm A F b).map i (MilnorK.normalizationBranchBoundary A F hdim b i a) := rfl

/-- In degree one, the excellent local boundary agrees with the concrete tame symbol. -/
theorem canonicalExcellentLocalBoundary_one
    (A F : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1)
    (z : MilnorK.DegreeTwoPresentation F) :
    canonicalExcellentLocalBoundary A F hdim 1 (MilnorK.degreeTwoMap F z) =
      MilnorK.degreeOneMap (IsLocalRing.ResidueField A)
        (MilnorK.boundaryOne A F hdim z) :=
  excellentLocalBoundary_one A F hdim (normalizationResidueMilnorNorm A F) z

end MilnorK
