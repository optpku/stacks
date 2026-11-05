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

open scoped BigOperators TensorProduct

universe u

namespace MilnorK.RationalFunction

abbrev Prime (k : Type u) [Field k] :=
  {p : Polynomial k // p.Monic ∧ Irreducible p}

instance primeFact (k : Type u) [Field k] (p : Prime k) : Fact (Irreducible p.1) :=
  ⟨p.2.2⟩

noncomputable abbrev primeIdeal (k : Type u) [Field k] (p : Prime k) : Ideal (Polynomial k) :=
  Ideal.span {p.1}

instance primeIdealPrime (k : Type u) [Field k] (p : Prime k) :
    (primeIdeal k p).IsPrime :=
  inferInstanceAs (Ideal.span {p.1}).IsPrime

instance primeDVR (k : Type u) [Field k] (p : Prime k) :
    IsDiscreteValuationRing (Localization.AtPrime (primeIdeal k p)) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    (Polynomial k)
    (fun (h : primeIdeal k p = ⊥) ↦ p.2.2.ne_zero (Ideal.span_singleton_eq_bot.mp h))
    (Localization.AtPrime (primeIdeal k p))

noncomputable def primeEvaluation (k : Type u) [Field k] (p : Prime k) :
    Localization.AtPrime (primeIdeal k p) →+* AdjoinRoot p.1 where
  toFun a :=
    let fraction := IsLocalization.sec (primeIdeal k p).primeCompl a
    AdjoinRoot.mk p.1 fraction.1 / AdjoinRoot.mk p.1 fraction.2.1
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

instance primeEvaluationLocal (k : Type u) [Field k] (p : Prime k) :
    IsLocalHom (primeEvaluation k p) := sorry

noncomputable def primeFractionMap (k : Type u) [Field k] (p : Prime k) :
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

noncomputable def primeResidue (k : Type u) [Field k] (p : Prime k) (i : ℕ) :
    Group (i + 1) (RatFunc k) →+ Group i (AdjoinRoot p.1) :=
  (mapGroup (IsLocalRing.ResidueField.lift (primeEvaluation k p)) i).comp
    ((dvrBoundary (Localization.AtPrime (primeIdeal k p))
      (FractionRing (Localization.AtPrime (primeIdeal k p))) i).comp
        (mapGroup (primeFractionMap k p) (i + 1)))


noncomputable def zeroPrime (k : Type u) [Field k] : Prime k :=
  ⟨Polynomial.X, Polynomial.monic_X, Polynomial.irreducible_X⟩

noncomputable def zeroEvaluation (k : Type u) [Field k] :
    Localization.AtPrime (primeIdeal k (zeroPrime k)) →+* k where
  toFun a :=
    let fraction := IsLocalization.sec (primeIdeal k (zeroPrime k)).primeCompl a
    fraction.1.eval 0 / fraction.2.1.eval 0
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

instance zeroEvaluationLocal (k : Type u) [Field k] :
    IsLocalHom (zeroEvaluation k) := sorry

noncomputable def invertVariable (k : Type u) [Field k] : RatFunc k →+* RatFunc k where
  toFun a :=
    a.num.eval₂ (RatFunc.C : k →+* RatFunc k) (RatFunc.X⁻¹) /
      a.denom.eval₂ (RatFunc.C : k →+* RatFunc k) (RatFunc.X⁻¹)
  map_zero' := sorry
  map_one' := sorry
  map_add' := sorry
  map_mul' := sorry

noncomputable def infinityResidue (k : Type u) [Field k] (i : ℕ) :
    Group (i + 1) (RatFunc k) →+ Group i k :=
  ((mapGroup (IsLocalRing.ResidueField.lift (zeroEvaluation k)) i).comp
    ((dvrBoundary (Localization.AtPrime (primeIdeal k (zeroPrime k)))
      (FractionRing (Localization.AtPrime (primeIdeal k (zeroPrime k)))) i).comp
        (mapGroup (primeFractionMap k (zeroPrime k)) (i + 1)))).comp
      (mapGroup (invertVariable k) (i + 1))

noncomputable def finiteResidues (k : Type u) [Field k] (i : ℕ)
    (a : Group (i + 1) (RatFunc k)) :
    (p : Prime k) → Group i (AdjoinRoot p.1) :=
  fun p ↦ primeResidue k p i a


/-- The canonical polynomial representative of a residue-field unit. -/
noncomputable def unitRepresentative (k : Type u) [Field k] (p : Prime k)
    (a : (AdjoinRoot p.1)ˣ) : Polynomial k :=
  AdjoinRoot.modByMonicHom p.2.1 (a : AdjoinRoot p.1)

theorem unitRepresentative_ne_zero (k : Type u) [Field k] (p : Prime k)
    (a : (AdjoinRoot p.1)ˣ) : unitRepresentative k p a ≠ 0 := by
  intro h
  have he := AdjoinRoot.mk_leftInverse p.2.1 (a : AdjoinRoot p.1)
  change AdjoinRoot.mk p.1 (unitRepresentative k p a) = (a : AdjoinRoot p.1) at he
  rw [h, map_zero] at he
  exact Units.ne_zero a he.symm

theorem unitRepresentative_natDegree_lt (k : Type u) [Field k] (p : Prime k)
    (a : (AdjoinRoot p.1)ˣ) : (unitRepresentative k p a).natDegree < p.1.natDegree := by
  have h := AdjoinRoot.mk_leftInverse p.2.1 (a : AdjoinRoot p.1)
  unfold unitRepresentative
  rw [← h, AdjoinRoot.modByMonicHom_mk]
  exact Polynomial.natDegree_modByMonic_lt _ p.2.1 p.2.2.ne_one

/-- Lift a residue-field unit using its polynomial remainder, with its explicit field inverse. -/
noncomputable def liftedUnit (k : Type u) [Field k] (p : Prime k)
    (a : (AdjoinRoot p.1)ˣ) : (RatFunc k)ˣ :=
  Units.mk0 (algebraMap (Polynomial k) (RatFunc k) (unitRepresentative k p a))
    (RatFunc.algebraMap_ne_zero (unitRepresentative_ne_zero k p a))

/-- Append the defining polynomial as the last entry of the lifted symbol. -/
noncomputable def liftedSymbolUnits (k : Type u) [Field k] (p : Prime k) (i : ℕ)
    (a : Fin i → Additive (AdjoinRoot p.1)ˣ) : Fin (i + 1) → (RatFunc k)ˣ :=
  Fin.lastCases
    (Units.mk0 (algebraMap (Polynomial k) (RatFunc k) p.1)
      (RatFunc.algebraMap_ne_zero p.2.2.ne_zero))
    (fun r ↦ liftedUnit k p (Additive.toMul (a r)))

/-- Distinct monic irreducible factors, using the existing normalized factorization owner. -/
noncomputable def primeFactors (k : Type u) [Field k] (f : Polynomial k) (hf : f ≠ 0) :
    Finset (Prime k) := by
  classical
  exact (UniqueFactorizationMonoid.normalizedFactors f).toFinset.attach.image fun q ↦
    let hq := (Polynomial.mem_normalizedFactors_iff hf).mp (Multiset.mem_toFinset.mp q.2)
    ⟨q.1, hq.2.1, hq.1⟩

theorem primeFactors_dvd (k : Type u) [Field k] (f : Polynomial k) (hf : f ≠ 0)
    (q : Prime k) (hq : q ∈ primeFactors k f hf) : q.1 ∣ f := by
  classical
  obtain ⟨r, _, he⟩ := Finset.mem_image.mp hq
  have hdvd := ((Polynomial.mem_normalizedFactors_iff hf).mp
    (Multiset.mem_toFinset.mp r.2)).2.2
  have heq : r.1 = q.1 := congrArg Subtype.val he
  simpa only [heq] using hdvd

/-- Every factor considered in the recursion has strictly smaller degree. Thus the filter
in `lowerPrimes` is not discarding any factor of the lifted unit entries. -/
theorem primeFactors_representatives_degree_lt (k : Type u) [Field k] (p : Prime k) (i : ℕ)
    (a : Fin i → Additive (AdjoinRoot p.1)ˣ) (q : Prime k)
    (hq : q ∈ primeFactors k (∏ r, unitRepresentative k p (Additive.toMul (a r)))
      (Finset.prod_ne_zero_iff.mpr fun r _ ↦
        unitRepresentative_ne_zero k p (Additive.toMul (a r)))) :
    q.1.natDegree < p.1.natDegree := by
  classical
  have hdvd := primeFactors_dvd k _ _ q hq
  obtain ⟨r, _, hr⟩ := (q.2.2.prime.dvd_finsetProd_iff _).mp hdvd
  exact (Polynomial.natDegree_le_of_dvd hr
    (unitRepresentative_ne_zero k p (Additive.toMul (a r)))).trans_lt
      (unitRepresentative_natDegree_lt k p (Additive.toMul (a r)))

/-- Only factors of the lifted unit entries can contribute away from the defining place.
The strict degree filter supplies the termination certificate without a chosen witness. -/
noncomputable def lowerPrimes (k : Type u) [Field k] (p : Prime k) (i : ℕ)
    (a : Fin i → Additive (AdjoinRoot p.1)ˣ) :
    Finset {q : Prime k // q.1.natDegree < p.1.natDegree} := by
  classical
  exact (primeFactors k (∏ r, unitRepresentative k p (Additive.toMul (a r)))
    (Finset.prod_ne_zero_iff.mpr fun r _ ↦
      unitRepresentative_ne_zero k p (Additive.toMul (a r)))).subtype
        (fun q ↦ q.1.natDegree < p.1.natDegree)

/-- One explicit summand of the finite-place tame symbol.  The coefficient and unit tuple
are the same normal-form data used by `MilnorK.dvrSymbolFormula`; no tensor representative
of a Milnor class is selected here. -/
noncomputable def primeSymbolTerm (k : Type u) [Field k] (q : Prime k) (i : ℕ)
    (x : Fin (i + 1) → (RatFunc k)ˣ)
    (S : {S : Finset (Fin (i + 1)) // S.Nonempty}) :
    ℤ × (Fin i → (AdjoinRoot q.1)ˣ) :=
  let A := Localization.AtPrime (primeIdeal k q)
  let F := FractionRing A
  let y := fun r ↦ Units.map (primeFractionMap k q).toMonoidHom (x r)
  let last := S.1.max' S.2
  ⟨((-1 : ℤ) ^ (i - last.1)) * ∏ r ∈ S.1, (dvrNormalForm A F (y r)).1,
    fun s ↦ Units.map (IsLocalRing.ResidueField.lift (primeEvaluation k q)).toMonoidHom
      (if last.succAbove s ∈ S.1 then -1 else dvrResidueUnit A F (y (last.succAbove s)))⟩

/-- The explicit Bass–Tate recursion on symbols: lift by polynomial remainders, take the
negative infinity residue, and subtract the already computed lower-degree contributions.
This is a function defined before imposing multilinearity or the Steinberg relations. -/
noncomputable def polynomialNormSymbol (k : Type u) [Field k] (p : Prime k) (i : ℕ)
    (a : Fin i → Additive (AdjoinRoot p.1)ˣ) : Group i k := by
  classical
  exact -infinityResidue k i (symbol (liftedSymbolUnits k p i a)) -
    ∑ q ∈ lowerPrimes k p i a,
      ∑ S : {S : Finset (Fin (i + 1)) // S.Nonempty},
        let term := primeSymbolTerm k q.1 i (liftedSymbolUnits k p i a) S
        term.1 • polynomialNormSymbol k q.1 i (fun r ↦ Additive.ofMul (term.2 r))
termination_by p.1.natDegree
decreasing_by exact q.2

/-- Additivity is an equation about the concrete recursive formula, not an existence
certificate used to select a norm. -/
theorem polynomialNormSymbol_update_add (k : Type u) [Field k] (p : Prime k) (i : ℕ)
    [DecidableEq (Fin i)]
    (a : Fin i → Additive (AdjoinRoot p.1)ˣ) (r : Fin i)
    (x y : Additive (AdjoinRoot p.1)ˣ) :
    polynomialNormSymbol k p i (Function.update a r (x + y)) =
      polynomialNormSymbol k p i (Function.update a r x) +
        polynomialNormSymbol k p i (Function.update a r y) := sorry

theorem polynomialNormSymbol_update_smul (k : Type u) [Field k] (p : Prime k) (i : ℕ)
    [DecidableEq (Fin i)]
    (a : Fin i → Additive (AdjoinRoot p.1)ˣ) (r : Fin i) (n : ℤ)
    (x : Additive (AdjoinRoot p.1)ˣ) :
    polynomialNormSymbol k p i (Function.update a r (n • x)) =
      n • polynomialNormSymbol k p i (Function.update a r x) := sorry

noncomputable def polynomialNormMultilinear (k : Type u) [Field k] (p : Prime k) (i : ℕ) :
    MultilinearMap ℤ (fun _ : Fin i ↦ Additive (AdjoinRoot p.1)ˣ) (Group i k) where
  toFun := polynomialNormSymbol k p i
  map_update_add' a r x y := polynomialNormSymbol_update_add k p i a r x y
  map_update_smul' a r n x := polynomialNormSymbol_update_smul k p i a r n x

noncomputable def polynomialNormTensor (k : Type u) [Field k] (p : Prime k) (i : ℕ) :
    (⨂[ℤ] _ : Fin i, Additive (AdjoinRoot p.1)ˣ) →ₗ[ℤ] Group i k :=
  PiTensorProduct.lift (polynomialNormMultilinear k p i)

/-- The recursive formula respects the given Milnor quotient presentation. -/
theorem polynomialNormTensor_ker (k : Type u) [Field k] (p : Prime k) (i : ℕ) :
    LinearMap.ker (tensorToRing i (AdjoinRoot p.1)) ≤
      LinearMap.ker (polynomialNormTensor k p i) := sorry

/-- Descend the explicit recursive formula using the canonical quotient-to-range
isomorphism of a linear map. Its inverse is mathlib's proved first isomorphism theorem;
the range identification is the definitionally proved `tensorToRing_range`. -/
noncomputable def polynomialNorm (k : Type u) [Field k] (p : Prime k) (i : ℕ) :
    Group i (AdjoinRoot p.1) →+ Group i k :=
  (((LinearMap.ker (tensorToRing i (AdjoinRoot p.1))).liftQ
      (polynomialNormTensor k p i) (polynomialNormTensor_ker k p i)).comp
    ((LinearEquiv.ofEq _ _ (tensorToRing_range i (AdjoinRoot p.1))).symm.trans
      (tensorToRing i (AdjoinRoot p.1)).quotKerEquivRange.symm).toLinearMap).toAddMonoidHom

/-- The quotient-to-range inverse is evaluated on an image by the explicit quotient class.
In particular this descent does not choose a tensor using an admitted surjectivity theorem. -/
theorem polynomialNorm_apply_tensor (k : Type u) [Field k] (p : Prime k) (i : ℕ)
    (t : ⨂[ℤ] _ : Fin i, Additive (AdjoinRoot p.1)ˣ) :
    polynomialNorm k p i ⟨tensorToRing i (AdjoinRoot p.1) t, ⟨t, rfl⟩⟩ =
      polynomialNormTensor k p i t := by
  change ((LinearMap.ker (tensorToRing i (AdjoinRoot p.1))).liftQ
    (polynomialNormTensor k p i) (polynomialNormTensor_ker k p i))
      ((tensorToRing i (AdjoinRoot p.1)).quotKerEquivRange.symm
        ⟨tensorToRing i (AdjoinRoot p.1) t, ⟨t, rfl⟩⟩) = _
  rw [LinearMap.quotKerEquivRange_symm_apply_image]
  rfl

/-- On a symbol the norm is exactly the degree-recursive formula given above. -/
theorem polynomialNorm_symbol (k : Type u) [Field k] (p : Prime k) (i : ℕ)
    (a : Fin i → Additive (AdjoinRoot p.1)ˣ) :
    polynomialNorm k p i (symbol (fun r ↦ Additive.toMul (a r))) =
      polynomialNormSymbol k p i a := by
  let t := PiTensorProduct.tprod ℤ a
  have hs : symbol (fun r ↦ Additive.toMul (a r)) =
      (⟨tensorToRing i (AdjoinRoot p.1) t, ⟨t, rfl⟩⟩ : Group i (AdjoinRoot p.1)) := by
    apply Subtype.ext
    change quotientMk (AdjoinRoot p.1) (TensorAlgebra.tprod ℤ _ i a) =
      quotientMk (AdjoinRoot p.1) (TensorPower.toTensorAlgebra (PiTensorProduct.tprod ℤ a))
    rw [TensorPower.toTensorAlgebra_tprod]
  rw [hs, polynomialNorm_apply_tensor]
  exact PiTensorProduct.lift.tprod a

end MilnorK.RationalFunction
