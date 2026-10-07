module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.FieldTheory.KummerPolynomial
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Smooth.Local
public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.LinearAlgebra.TensorProduct.Surjective
public import ReasLib.FieldTheory.RatFunc.Degree
public import ReasLib.RingTheory.AlgHom.Local.AtPrime
public import ReasLib.RingTheory.Kaehler.CharP
public import ReasLib.RingTheory.LocalRing.DimensionOne
public import ReasLib.RingTheory.MvPolynomial.Fin
public import ReasLib.RingTheory.Polynomial.ConstantCoeff

/-!
# Positive-characteristic smoothness counterexamples

@stack 00TY

This file records the two explicit algebras and the closed point used in the
source example.  Proof-specific normal forms, localization maps, and
cotangent-complex comparison maps are deliberately left to the proof stage.
-/

@[expose] public section

open scoped RatFunc
open scoped TensorProduct

noncomputable section

namespace Algebra.CharP.Example_10_140_8

section

variable (p : ℕ) [Fact p.Prime]

namespace NilpotentQuotient

/-- The quotient `F_p[x]/(x^p)` in Example 10.140.8. -/
abbrev ring : Type :=
  Polynomial (ZMod p) ⧸
    Ideal.span ({Polynomial.X ^ p} : Set (Polynomial (ZMod p)))

private abbrev polynomialRing : Type := Polynomial (ZMod p)

private abbrev relationIdeal : Ideal (polynomialRing p) :=
  Ideal.span ({Polynomial.X ^ p} : Set (polynomialRing p))

private theorem quotientMap_surjective :
    Function.Surjective (algebraMap (polynomialRing p) (ring p)) := by
  simpa [polynomialRing, ring, relationIdeal] using
    (Ideal.Quotient.mkₐ_surjective (ZMod p) (relationIdeal p))

private theorem quotientMap_ker :
    RingHom.ker (algebraMap (polynomialRing p) (ring p)) = relationIdeal p := by
  simpa [polynomialRing, ring, relationIdeal] using
    (Ideal.Quotient.mkₐ_ker (ZMod p) (relationIdeal p))

private theorem relation_mem_ker :
    Polynomial.X ^ p ∈
      RingHom.ker (algebraMap (polynomialRing p) (ring p)) := by
  rw [quotientMap_ker]
  exact Ideal.subset_span (Set.mem_singleton _)

private theorem tensor_D_relation_mul_eq_zero (c : polynomialRing p) :
    (1 : ring p) ⊗ₜ[polynomialRing p]
      KaehlerDifferential.D (ZMod p) (polynomialRing p) (Polynomial.X ^ p * c) = 0 := by
  rw [Derivation.leibniz, KaehlerDifferential.CharP.D_X_pow_eq_zero]
  simp only [smul_zero, add_zero, TensorProduct.tmul_smul]
  have hrelation :
      algebraMap (polynomialRing p) (ring p) (Polynomial.X ^ p) = 0 := by
    rw [← RingHom.mem_ker]
    exact relation_mem_ker p
  have hleft : (Polynomial.X ^ p : polynomialRing p) • (1 : ring p) = 0 := by
    change algebraMap (polynomialRing p) (ring p) (Polynomial.X ^ p) * 1 = 0
    rw [hrelation, zero_mul]
  exact
    (congrArg
      (fun y : ring p ↦ y ⊗ₜ[polynomialRing p]
        KaehlerDifferential.D (ZMod p) (polynomialRing p) c) hleft).trans
      (TensorProduct.zero_tmul _ _)

private theorem tensor_D_eq_zero
    (x : RingHom.ker (algebraMap (polynomialRing p) (ring p))) :
    (1 : ring p) ⊗ₜ[polynomialRing p]
      KaehlerDifferential.D (ZMod p) (polynomialRing p) x.1 = 0 := by
  have hx : x.1 ∈ relationIdeal p := by
    rw [← quotientMap_ker]
    exact x.2
  rw [relationIdeal, Ideal.mem_span_singleton] at hx
  obtain ⟨c, hc⟩ := hx
  rw [hc]
  exact tensor_D_relation_mul_eq_zero p c

private theorem conormalMap_toCotangent_eq_zero
    (x : RingHom.ker (algebraMap (polynomialRing p) (ring p))) :
    KaehlerDifferential.kerCotangentToTensor (ZMod p) (polynomialRing p) (ring p)
      ((RingHom.ker (algebraMap (polynomialRing p) (ring p))).toCotangent x) = 0 := by
  rw [KaehlerDifferential.kerCotangentToTensor_toCotangent]
  exact tensor_D_eq_zero p x

private theorem conormalClass_ne_zero :
    (RingHom.ker (algebraMap (polynomialRing p) (ring p))).toCotangent
      ⟨Polynomial.X ^ p, relation_mem_ker p⟩ ≠ 0 := by
  intro hzero
  rw [Ideal.toCotangent_eq_zero] at hzero
  have hmem : Polynomial.X ^ p ∈ (relationIdeal p) ^ 2 := by
    simpa [quotientMap_ker] using hzero
  rw [relationIdeal, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_two, ← pow_add] at hmem
  have hlt : p < p + p := lt_add_of_pos_right p (Fact.out : Nat.Prime p).pos
  have hcoeff := (Polynomial.X_pow_dvd_iff.mp hmem) p hlt
  simpa using hcoeff

private theorem mapBaseChange_bijective :
    Function.Bijective
      (KaehlerDifferential.mapBaseChange (ZMod p) (polynomialRing p) (ring p)) := by
  have hExact := KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange
    (ZMod p) (polynomialRing p) (ring p) (quotientMap_surjective p)
  have hConormalRange :
      LinearMap.range (KaehlerDifferential.kerCotangentToTensor
        (ZMod p) (polynomialRing p) (ring p)) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := Ideal.toCotangent_surjective
      (RingHom.ker (algebraMap (polynomialRing p) (ring p))) z
    exact conormalMap_toCotangent_eq_zero p x
  have hKerRestrict :
      LinearMap.ker
          ((KaehlerDifferential.mapBaseChange (ZMod p) (polynomialRing p) (ring p)).restrictScalars
            (polynomialRing p)) = ⊥ := by
    calc
      LinearMap.ker
          ((KaehlerDifferential.mapBaseChange
            (ZMod p) (polynomialRing p) (ring p)).restrictScalars (polynomialRing p)) =
          LinearMap.range (KaehlerDifferential.kerCotangentToTensor
            (ZMod p) (polynomialRing p) (ring p)) :=
        Function.Exact.linearMap_ker_eq hExact
      _ = ⊥ := hConormalRange
  refine ⟨?_, KaehlerDifferential.mapBaseChange_surjective
    (ZMod p) (polynomialRing p) (ring p) (quotientMap_surjective p)⟩
  intro x y hxy
  apply sub_eq_zero.mp
  have hmem : x - y ∈ LinearMap.ker
      ((KaehlerDifferential.mapBaseChange (ZMod p) (polynomialRing p) (ring p)).restrictScalars
        (polynomialRing p)) := by
    rw [LinearMap.mem_ker]
    simp [hxy]
  simpa [hKerRestrict] using hmem

/-- Example 10.140.8 (1): the quotient `F_p[x]/(x^p)` has free module of Kähler
differentials over `F_p`. -/
@[stacks 00TY "(1)"]
theorem kaehlerDifferential_free :
    Module.Free (ring p) Ω[ring p⁄ZMod p] := by
  let e := LinearEquiv.ofBijective
    (KaehlerDifferential.mapBaseChange (ZMod p) (polynomialRing p) (ring p))
    (mapBaseChange_bijective p)
  exact Module.Free.of_equiv e

/-- Example 10.140.8 (2): the quotient `F_p[x]/(x^p)` is not smooth over `F_p`. -/
@[stacks 00TY "(2)"]
theorem not_smooth : ¬ Smooth (ZMod p) (ring p) := by
  intro hsmooth
  have hFormal : Algebra.FormallySmooth (ZMod p) (ring p) :=
    Algebra.Smooth.formallySmooth
  obtain ⟨l, hl⟩ :=
    (Algebra.FormallySmooth.iff_split_injection (quotientMap_surjective p)).mp hFormal
  let x :=
    (RingHom.ker (algebraMap (polynomialRing p) (ring p))).toCotangent
      ⟨Polynomial.X ^ p, relation_mem_ker p⟩
  apply conormalClass_ne_zero p
  have hx := LinearMap.congr_fun hl x
  have hmapx :
      KaehlerDifferential.kerCotangentToTensor (ZMod p) (polynomialRing p) (ring p) x = 0 := by
    exact conormalMap_toCotangent_eq_zero p
      ⟨Polynomial.X ^ p, relation_mem_ker p⟩
  rw [LinearMap.comp_apply, hmapx, map_zero, LinearMap.id_apply] at hx
  exact hx.symm

end NilpotentQuotient

namespace PlaneCurve

/-- The coefficient field `F_p(t)` in the plane-curve part of Example 10.140.8. -/
abbrev coeffField : Type := RatFunc (ZMod p)

/-- The bivariate polynomial ring over `F_p(t)` with coordinates `x` and `y`. -/
abbrev coordRing : Type := MvPolynomial (Fin 2) (coeffField p)

/-- The equation `x^p + y^2 + t` of the plane curve in Example 10.140.8. -/
abbrev equation : coordRing p :=
  MvPolynomial.X (0 : Fin 2) ^ p + MvPolynomial.X (1 : Fin 2) ^ 2 +
    MvPolynomial.C (RatFunc.X : coeffField p)

/-- The plane-curve quotient `F_p(t)[x,y]/(x^p+y^2+t)`. -/
abbrev quotient : Type :=
  coordRing p ⧸ Ideal.span ({equation p} : Set (coordRing p))

/-- The canonical algebra quotient map defining the plane-curve ring. -/
abbrev quotientMap : coordRing p →ₐ[coeffField p] quotient p :=
  Ideal.Quotient.mkₐ (coeffField p)
    (Ideal.span ({equation p} : Set (coordRing p)))

/-- The kernel of the canonical quotient map is the displayed plane-curve relation ideal. -/
theorem quotientMap_ker :
  RingHom.ker (quotientMap p).toRingHom =
      Ideal.span ({equation p} : Set (coordRing p)) := by
  exact Ideal.Quotient.mkₐ_ker (coeffField p)
    (Ideal.span ({equation p} : Set (coordRing p)))

/-- The canonical plane-curve quotient map is surjective. -/
theorem quotientMap_surjective : Function.Surjective (quotientMap p) := by
  exact Ideal.Quotient.mkₐ_surjective (coeffField p)
    (Ideal.span ({equation p} : Set (coordRing p)))

private abbrev xRelation : coordRing p :=
  MvPolynomial.X (0 : Fin 2) ^ p +
    MvPolynomial.C (RatFunc.X : coeffField p)

private abbrev y : coordRing p := MvPolynomial.X (1 : Fin 2)

private abbrev adjoinPolynomial : Polynomial (coeffField p) :=
  Polynomial.X ^ p + Polynomial.C (RatFunc.X : coeffField p)

private theorem adjoinPolynomial_irreducible :
    Irreducible (adjoinPolynomial p) := by
  have hrewrite :
      (Polynomial.X ^ p -
          Polynomial.C (-(RatFunc.X : coeffField p)) :
        Polynomial (coeffField p)) = adjoinPolynomial p := by
    simp [adjoinPolynomial, sub_eq_add_neg]
  rw [← hrewrite]
  exact X_pow_sub_C_irreducible_of_prime (Fact.out : Nat.Prime p)
    (RatFunc.neg_X_not_pow p (Fact.out : Nat.Prime p).one_lt)

private noncomputable def coeffEquiv :
    MvPolynomial (Fin 1) (coeffField p) ≃ₐ[coeffField p]
      Polynomial (coeffField p) :=
  MvPolynomial.uniqueAlgEquiv (coeffField p) (Fin 1)

private noncomputable def normalForm :
    coordRing p ≃ₐ[coeffField p]
      Polynomial (Polynomial (coeffField p)) :=
  (MvPolynomial.Fin.lastVariableEquiv (A := coeffField p) 1).trans
    (Polynomial.mapAlgEquiv (coeffEquiv p))

@[simp]
private theorem normalForm_x :
    normalForm p (MvPolynomial.X (0 : Fin 2)) =
      Polynomial.C Polynomial.X := by
  change normalForm p (MvPolynomial.X (Fin.castSucc (0 : Fin 1))) = _
  simp only [normalForm, AlgEquiv.trans_apply,
    MvPolynomial.Fin.lastVariableEquiv_X_castSucc,
    Polynomial.coe_mapAlgEquiv, Polynomial.map_C]
  congr 1
  simp [coeffEquiv, MvPolynomial.uniqueAlgEquiv]

@[simp]
private theorem normalForm_y :
    normalForm p (y p) = Polynomial.X := by
  change normalForm p (MvPolynomial.X (Fin.last 1)) = _
  simp only [normalForm, AlgEquiv.trans_apply,
    MvPolynomial.Fin.lastVariableEquiv_X_last,
    Polynomial.coe_mapAlgEquiv, Polynomial.map_X]

@[simp]
private theorem normalForm_C (a : coeffField p) :
    normalForm p (MvPolynomial.C a) = Polynomial.C (Polynomial.C a) := by
  simpa using (normalForm p).commutes a

@[simp]
private theorem normalForm_xRelation :
    normalForm p (xRelation p) = Polynomial.C (adjoinPolynomial p) := by
  simp [xRelation, adjoinPolynomial]

private abbrev normalEquation : Polynomial (Polynomial (coeffField p)) :=
  Polynomial.C (adjoinPolynomial p) + Polynomial.X ^ 2

@[simp]
private theorem normalForm_equation :
    normalForm p (equation p) = normalEquation p := by
  simp [equation, normalEquation, add_assoc, add_comm]

private theorem adjoinPolynomial_notMem_span_sq :
    adjoinPolynomial p ∉
      (Ideal.span ({adjoinPolynomial p} : Set (Polynomial (coeffField p)))) ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  intro hdiv
  have hdegree_le := Polynomial.natDegree_le_of_dvd
    (p := adjoinPolynomial p ^ 2) (q := adjoinPolynomial p) hdiv
    (adjoinPolynomial_irreducible p).ne_zero
  have hdegree : (adjoinPolynomial p).natDegree = p := by
    simp [adjoinPolynomial]
  rw [Polynomial.natDegree_pow, hdegree] at hdegree_le
  have hlt : p < 2 * p := by
    simpa [two_mul] using lt_add_of_pos_right p (Fact.out : Nat.Prime p).pos
  exact (Nat.not_le_of_gt hlt) hdegree_le

private theorem normalEquation_prime : Prime (normalEquation p) := by
  let K := coeffField p
  let g : Polynomial K := adjoinPolynomial p
  let f : Polynomial (Polynomial K) := Polynomial.C g + Polynomial.X ^ 2
  have hmonic : f.Monic := by
    simpa [f, g, pow_two, add_comm] using
      Polynomial.monic_X_pow_add_C (R := Polynomial K) (n := 2) g
  have hprimeIdeal : (Ideal.span ({g} : Set (Polynomial K))).IsPrime := by
    rw [Ideal.span_singleton_prime]
    · exact (adjoinPolynomial_irreducible p).prime
    · exact (adjoinPolynomial_irreducible p).ne_zero
  have hnotMemSq : f.coeff 0 ∉ (Ideal.span ({g} : Set (Polynomial K))) ^ 2 := by
    simp only [f, Polynomial.coeff_add, Polynomial.coeff_C_zero, Polynomial.coeff_X_pow]
    simpa [g] using adjoinPolynomial_notMem_span_sq p
  have hnatDegree : f.natDegree = 2 := by
    simpa [f, g, add_comm] using
      Polynomial.natDegree_X_pow_add_C (R := Polynomial K) (n := 2) (r := g)
  have heisenstein : f.IsEisensteinAt (Ideal.span ({g} : Set (Polynomial K))) := by
    refine hmonic.isEisensteinAt_of_mem_of_notMem hprimeIdeal.ne_top ?_ hnotMemSq
    intro n hn
    rw [hnatDegree] at hn
    have hn_le : n ≤ 1 := by
      exact Nat.lt_succ_iff.mp (show n < Nat.succ 1 by simpa using hn)
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hn_le with rfl | rfl
    · simpa [f] using Ideal.subset_span (Set.mem_singleton g)
    · simp [f]
  have hirreducible : Irreducible f := by
    apply heisenstein.irreducible hprimeIdeal hmonic.isPrimitive
    rw [hnatDegree]
    decide
  simpa [f, g, normalEquation] using hirreducible.prime

private theorem equation_ne_zero : equation p ≠ 0 := by
  intro hzero
  have hnormal := congrArg (normalForm p) hzero
  rw [normalForm_equation, map_zero] at hnormal
  exact (normalEquation_prime p).ne_zero hnormal

private theorem normalForm_map_relationIdeal :
    Ideal.map (normalForm p).toRingEquiv.toRingHom
        (Ideal.span ({equation p} : Set (coordRing p))) =
      Ideal.span ({normalEquation p} : Set (Polynomial (Polynomial (coeffField p)))) := by
  rw [Ideal.map_span]
  congr 1
  ext z
  simp [normalForm_equation]

private noncomputable def quotientNormalEquiv :
    quotient p ≃ₐ[coeffField p] AdjoinRoot (normalEquation p) :=
  Ideal.quotientEquivAlg
    (I := Ideal.span ({equation p} : Set (coordRing p)))
    (J := Ideal.span ({normalEquation p} : Set (Polynomial (Polynomial (coeffField p)))))
    (normalForm p) (normalForm_map_relationIdeal p).symm

private theorem quotient_isDomain : IsDomain (quotient p) := by
  letI : IsDomain (AdjoinRoot (normalEquation p)) :=
    AdjoinRoot.isDomain_of_prime (normalEquation_prime p)
  exact (quotientNormalEquiv p).toRingEquiv.toMulEquiv.isDomain _

private theorem quotientNormalEquiv_apply_y :
    quotientNormalEquiv p (quotientMap p (y p)) = AdjoinRoot.root (normalEquation p) := by
  unfold quotientNormalEquiv
  have hmk := Ideal.quotientEquivAlg_mk
    (I := Ideal.span ({equation p} : Set (coordRing p)))
    (J := Ideal.span ({normalEquation p} : Set (Polynomial (Polynomial (coeffField p)))))
    (normalForm p) (normalForm_map_relationIdeal p).symm (y p)
  calc
    (Ideal.quotientEquivAlg
        (Ideal.span ({equation p} : Set (coordRing p)))
        (Ideal.span ({normalEquation p} : Set (Polynomial (Polynomial (coeffField p)))))
        (normalForm p) (normalForm_map_relationIdeal p).symm)
        (quotientMap p (y p)) = normalForm p (y p) := by
      simpa [quotientMap] using hmk
    _ = AdjoinRoot.root (normalEquation p) := by
      rw [normalForm_y]
      rfl

private theorem y_ne_zero : quotientMap p (y p) ≠ 0 := by
  intro hy
  have hroot_zero := congrArg (quotientNormalEquiv p) hy
  have hroot_ne : AdjoinRoot.root (normalEquation p) ≠ 0 := by
    have hmonic : (normalEquation p).Monic := by
      simpa [normalEquation, pow_two, add_comm] using
        Polynomial.monic_X_pow_add_C
          (R := Polynomial (coeffField p)) (n := 2) (adjoinPolynomial p)
    have hdegree : (normalEquation p).degree = 2 := by
      simpa [normalEquation, add_comm] using
        Polynomial.degree_X_pow_add_C
          (R := Polynomial (coeffField p)) (n := 2) (by decide) (adjoinPolynomial p)
    change (AdjoinRoot.mk (normalEquation p))
      (Polynomial.X : Polynomial (Polynomial (coeffField p))) ≠ 0
    apply AdjoinRoot.mk_ne_zero_of_degree_lt hmonic Polynomial.X_ne_zero
    rw [Polynomial.degree_X, hdegree]
    decide
  apply hroot_ne
  rw [quotientNormalEquiv_apply_y] at hroot_zero
  simpa using hroot_zero

private def sourceIdeal : Ideal (coordRing p) :=
  Ideal.span ({xRelation p, y p} : Set (coordRing p))

private theorem sourceIdeal_isMaximal : (sourceIdeal p).IsMaximal := by
  rw [← Ideal.isMaximal_map_iff_of_bijective
    (f := (normalForm p).toRingEquiv.toRingHom) (normalForm p).bijective]
  rw [sourceIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change (Ideal.span ({normalForm p (xRelation p), normalForm p (y p)} :
    Set (Polynomial (Polynomial (coeffField p))))).IsMaximal
  rw [normalForm_xRelation, normalForm_y]
  exact AdjoinRoot.span_C_X_isMaximal (adjoinPolynomial p)
    (adjoinPolynomial_irreducible p)

private theorem equation_mem_sourceIdeal : equation p ∈ sourceIdeal p := by
  have hx : xRelation p ∈ sourceIdeal p :=
    Ideal.subset_span (Set.mem_insert _ _)
  have hy : y p ∈ sourceIdeal p :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  simpa [equation, xRelation, y, pow_two, add_assoc, add_left_comm, add_comm] using
    Ideal.add_mem (sourceIdeal p) hx
      (Ideal.mul_mem_left (sourceIdeal p) (y p) hy)

/-- The source ideal `q = (y, x^p + t)` in the plane-curve quotient. -/
def primeIdeal : Ideal (quotient p) :=
  Ideal.span
    ({ quotientMap p (MvPolynomial.X (1 : Fin 2)),
       quotientMap p
        (MvPolynomial.X (0 : Fin 2) ^ p +
          MvPolynomial.C (RatFunc.X : coeffField p)) } : Set (quotient p))

private theorem xRelation_image_eq_neg_y_sq :
    quotientMap p (xRelation p) = -(quotientMap p (y p)) ^ 2 := by
  have hrel : quotientMap p (equation p) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  have hpoly : xRelation p + y p ^ 2 = equation p := by
    change
      (MvPolynomial.X (0 : Fin 2) ^ p + MvPolynomial.C RatFunc.X) +
          MvPolynomial.X (1 : Fin 2) ^ 2 =
        (MvPolynomial.X (0 : Fin 2) ^ p + MvPolynomial.X (1 : Fin 2) ^ 2) +
          MvPolynomial.C RatFunc.X
    exact add_right_comm _ _ _
  have hsum : quotientMap p (xRelation p + y p ^ 2) = 0 := by
    rw [hpoly]
    exact hrel
  rw [eq_neg_iff_add_eq_zero]
  simpa only [map_add, map_pow] using hsum

private theorem primeIdeal_eq_span_y :
    primeIdeal p = Ideal.span ({quotientMap p (y p)} : Set (quotient p)) := by
  apply le_antisymm
  · refine Ideal.span_le.mpr ?_
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact Ideal.subset_span (Set.mem_singleton _)
    · have hy : quotientMap p (y p) ∈
          Ideal.span ({quotientMap p (y p)} : Set (quotient p)) :=
        Ideal.subset_span (Set.mem_singleton _)
      have hy2 : quotientMap p (y p) ^ 2 ∈
          Ideal.span ({quotientMap p (y p)} : Set (quotient p)) := by
        simpa [pow_two] using
          (Ideal.span ({quotientMap p (y p)} : Set (quotient p))).mul_mem_left
            (quotientMap p (y p)) hy
      exact (xRelation_image_eq_neg_y_sq p).symm ▸
        (Ideal.span ({quotientMap p (y p)} : Set (quotient p))).neg_mem hy2
  · refine Ideal.span_le.mpr ?_
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    subst a
    exact Ideal.subset_span (Set.mem_insert _ _)

private theorem primeIdeal_eq_map_sourceIdeal :
    primeIdeal p = (sourceIdeal p).map (quotientMap p).toRingHom := by
  rw [primeIdeal, sourceIdeal, Ideal.map_span, Set.image_insert_eq, Set.image_singleton]
  change Ideal.span ({quotientMap p (y p), quotientMap p (xRelation p)} :
      Set (quotient p)) =
    Ideal.span ({quotientMap p (xRelation p), quotientMap p (y p)} :
      Set (quotient p))
  exact Ideal.span_pair_comm

/-- The displayed plane-curve ideal is maximal. -/
theorem primeIdeal_isMaximal : (primeIdeal p).IsMaximal := by
  rw [primeIdeal_eq_map_sourceIdeal]
  letI : (sourceIdeal p).IsMaximal := sourceIdeal_isMaximal p
  apply Ideal.IsMaximal.map_of_surjective_of_ker_le (quotientMap_surjective p)
  change RingHom.ker (quotientMap p).toRingHom ≤ sourceIdeal p
  rw [quotientMap_ker]
  exact Ideal.span_le.2 fun f hf ↦
    Set.mem_singleton_iff.mp hf ▸ equation_mem_sourceIdeal p

/-- The closed point determined by `q = (y, x^p + t)`. -/
def closedPoint : MaximalSpectrum (quotient p) :=
  ⟨primeIdeal p, primeIdeal_isMaximal p⟩

/-- The source-facing prime-spectrum view of the plane-curve closed point. -/
abbrev prime : PrimeSpectrum (quotient p) := (closedPoint p).toPrimeSpectrum

private theorem local_maximalIdeal_eq_span_y :
    IsLocalRing.maximalIdeal (Localization.AtPrime (prime p).asIdeal) =
      Ideal.span
        ({algebraMap (quotient p) (Localization.AtPrime (prime p).asIdeal)
          (quotientMap p (y p))} : Set (Localization.AtPrime (prime p).asIdeal)) := by
  let f : quotient p →+* Localization.AtPrime (prime p).asIdeal :=
    algebraMap (quotient p) (Localization.AtPrime (prime p).asIdeal)
  have hq : (prime p).asIdeal =
      Ideal.span ({quotientMap p (y p)} : Set (quotient p)) := by
    change primeIdeal p = Ideal.span ({quotientMap p (y p)} : Set (quotient p))
    exact primeIdeal_eq_span_y p
  calc
    IsLocalRing.maximalIdeal (Localization.AtPrime (prime p).asIdeal) =
        Ideal.map f (prime p).asIdeal :=
      (Localization.AtPrime.map_eq_maximalIdeal (I := (prime p).asIdeal)).symm
    _ = Ideal.map f (Ideal.span ({quotientMap p (y p)} : Set (quotient p))) := by
      exact congrArg (Ideal.map f) hq
    _ = Ideal.span
        ({algebraMap (quotient p) (Localization.AtPrime (prime p).asIdeal)
          (quotientMap p (y p))} : Set (Localization.AtPrime (prime p).asIdeal)) := by
      rw [Ideal.map_span]
      simpa only [f, Set.image_singleton]

private theorem local_y_ne_zero :
    algebraMap (quotient p) (Localization.AtPrime (prime p).asIdeal)
      (quotientMap p (y p)) ≠ 0 := by
  letI : IsDomain (quotient p) := quotient_isDomain p
  have hinjective : Function.Injective
      (algebraMap (quotient p) (Localization.AtPrime (prime p).asIdeal)) :=
    IsLocalization.injective (S := Localization.AtPrime (prime p).asIdeal)
      (prime p).asIdeal.primeCompl_le_nonZeroDivisors
  exact fun hzero ↦ y_ne_zero p (hinjective (by simpa using hzero))

private theorem local_not_isArtinian :
    ¬ IsArtinianRing (Localization.AtPrime (prime p).asIdeal) := by
  let L := Localization.AtPrime (prime p).asIdeal
  let yL : L := algebraMap (quotient p) L (quotientMap p (y p))
  letI : IsDomain (quotient p) := quotient_isDomain p
  letI : IsDomain L := IsLocalization.isDomain_of_le_nonZeroDivisors _
    (prime p).asIdeal.primeCompl_le_nonZeroDivisors
  intro hArtinian
  obtain ⟨n, hn⟩ :=
    (isArtinianRing_iff_isNilpotent_maximalIdeal L).mp hArtinian
  have hy_mem : yL ∈ IsLocalRing.maximalIdeal L := by
    rw [local_maximalIdeal_eq_span_y]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hy_pow_mem : yL ^ n ∈ (IsLocalRing.maximalIdeal L) ^ n :=
    Ideal.pow_mem_pow hy_mem n
  have hy_pow_zero : yL ^ n = 0 := by simpa [hn] using hy_pow_mem
  exact pow_ne_zero n (by simpa [L, yL] using local_y_ne_zero p) hy_pow_zero

private abbrev sourcePoint : PrimeSpectrum (coordRing p) :=
  PrimeSpectrum.comap (quotientMap p).toRingHom (prime p)

private abbrev sourceLocalRing : Type :=
  (quotientMap p).toRingHom.sourceLocalRingAt (prime p)

private abbrev targetLocalRing : Type :=
  Localization.AtPrime (prime p).asIdeal

private noncomputable def localMap : sourceLocalRing p →ₐ[coeffField p] targetLocalRing p :=
  (quotientMap p).localAlgHomAt (prime p)

private abbrev localizedEquation : sourceLocalRing p :=
  algebraMap (coordRing p) (sourceLocalRing p) (equation p)

private theorem differential_localizedEquation
    {T : Type*} [CommRing T] [Algebra (coordRing p) T]
    [Algebra (coeffField p) T]
    [IsScalarTower (coeffField p) (coordRing p) T] :
    KaehlerDifferential.D (coeffField p) T
        (algebraMap (coordRing p) T (equation p)) =
      (algebraMap (coordRing p) T (2 : coordRing p) *
        algebraMap (coordRing p) T (y p)) •
        KaehlerDifferential.D (coeffField p) T
          (algebraMap (coordRing p) T (y p)) := by
  simp only [equation, y, map_add, Fin.isValue, map_pow,
    Derivation.leibniz_pow, Nat.add_one_sub_one, pow_one, algebraMap_smul]
  have hpT : (p : T) = 0 := by
    rw [← map_natCast (algebraMap (coeffField p) T)]
    rw [CharP.cast_eq_zero (coeffField p) p, map_zero]
  rw [← Nat.cast_smul_eq_nsmul T p, hpT, zero_smul, zero_add]
  have hconst :
      KaehlerDifferential.D (coeffField p) T
        (algebraMap (coordRing p) T
          (MvPolynomial.C (RatFunc.X : coeffField p))) = 0 := by
    rw [← MvPolynomial.algebraMap_eq (coeffField p) (Fin 2)]
    rw [← IsScalarTower.algebraMap_apply
      (coeffField p) (coordRing p) T (RatFunc.X : coeffField p)]
    exact Derivation.map_algebraMap
      (KaehlerDifferential.D (coeffField p) T) (RatFunc.X : coeffField p)
  rw [hconst, add_zero, mul_smul]
  have htwo : algebraMap (coordRing p) T (2 : coordRing p) = (2 : T) :=
    map_ofNat (algebraMap (coordRing p) T) 2
  rw [htwo, ← Nat.cast_smul_eq_nsmul T 2]
  let v := KaehlerDifferential.D (coeffField p) T
    (algebraMap (coordRing p) T (y p))
  have hy_smul :
      (y p : coordRing p) • v = algebraMap (coordRing p) T (y p) • v :=
    (algebraMap_smul T (y p) v).symm
  exact congrArg (fun w ↦ (2 : T) • w) hy_smul

private theorem residueField_algebraMap_surjective
    {R S : Type*} [CommRing R] [CommRing S] [IsLocalRing S] [Algebra R S]
    (hsurjective : Function.Surjective (algebraMap R S)) :
    Function.Surjective (algebraMap R (IsLocalRing.ResidueField S)) := by
  intro z
  obtain ⟨s, rfl⟩ :=
    (Ideal.Quotient.mk_surjective (I := IsLocalRing.maximalIdeal S) :
      Function.Surjective (Ideal.Quotient.mk (IsLocalRing.maximalIdeal S))) z
  obtain ⟨r, rfl⟩ := hsurjective s
  exact ⟨r, rfl⟩

set_option maxHeartbeats 400000 in
/-- The bound-free core of Example 10.140.8 (3): the plane curve is not smooth
at `q = (y, x^p + t)`. -/
theorem not_isSmoothAt :
    ¬ IsSmoothAt (coeffField p) (prime p).asIdeal := by
  intro hsmooth
  let P := sourceLocalRing p
  let S := targetLocalRing p
  let K := IsLocalRing.ResidueField S
  letI : Algebra P S :=
    RingHom.toAlgebra (localMap p).toRingHom
  letI : IsScalarTower (coeffField p) P S :=
    IsScalarTower.of_algebraMap_eq fun r ↦ (localMap p).commutes r |>.symm
  letI : Algebra S K := RingHom.toAlgebra (IsLocalRing.residue S)
  letI : Algebra P K :=
    RingHom.toAlgebra
      ((IsLocalRing.residue S).comp (localMap p).toRingHom)
  letI : IsScalarTower P S K :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsurjective :
      Function.Surjective (algebraMap P S) := by
    change Function.Surjective (localMap p).toRingHom
    exact AlgHom.localAlgHomAt.surjective (quotientMap p)
      (quotientMap_surjective p) (prime p)
  have hker :
      RingHom.ker (algebraMap P S) =
        Ideal.span ({localizedEquation p} : Set P) := by
    calc
      RingHom.ker (algebraMap P S) =
          RingHom.ker (localMap p).toRingHom := rfl
      _ = (quotientMap p).toRingHom.localKernelIdealAt (prime p) :=
        AlgHom.localAlgHomAt.ker (quotientMap p) (quotientMap_surjective p) (prime p)
      _ = Ideal.span ({localizedEquation p} : Set P) :=
        RingHom.localKernelIdealAt.eq_span_singleton_of_ker_eq_span
          (quotientMap p).toRingHom (prime p) (equation p) (quotientMap_ker p)
  have hf_mem : localizedEquation p ∈
      RingHom.ker (algebraMap P S) := by
    rw [hker]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hf_ne : localizedEquation p ≠ 0 := by
    have hinjective : Function.Injective
        (algebraMap (coordRing p) P) :=
      IsLocalization.injective (S := P)
        (sourcePoint p).asIdeal.primeCompl_le_nonZeroDivisors
    exact fun hzero ↦ equation_ne_zero p (hinjective (by simpa using hzero))
  have hfiniteP : Module.Finite P Ω[P⁄coeffField p] :=
    KaehlerDifferential.finite (coeffField p) P
  have hprojectiveP : Module.Projective P Ω[P⁄coeffField p] :=
    Algebra.FormallySmooth.projective_kaehlerDifferential
      (R := coeffField p) (A := P)
  letI : Module.Finite P Ω[P⁄coeffField p] := hfiniteP
  letI : Module.Projective P Ω[P⁄coeffField p] := hprojectiveP
  have hfreeP : Module.Free P Ω[P⁄coeffField p] :=
    Module.free_of_flat_of_isLocalRing
  letI : Module.Free P Ω[P⁄coeffField p] := hfreeP
  have hfg : (RingHom.ker (algebraMap P S)).FG :=
    (RingHom.ker (algebraMap P S)).fg_of_isNoetherianRing
  have hinjective : Function.Injective
      (KaehlerDifferential.cotangentComplexBaseChange
        (coeffField p) S P K) :=
    (Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange_residueField
      (R := coeffField p) (S := S) (P := P)
      hsurjective hfg).mp hsmooth
  let xKer : RingHom.ker (algebraMap P S) :=
    ⟨localizedEquation p, hf_mem⟩
  let yP : P := algebraMap (coordRing p) P (y p)
  let a : P := algebraMap (coordRing p) P (2 : coordRing p) * yP
  have hy_source : y p ∈ (sourcePoint p).asIdeal := by
    change quotientMap p (y p) ∈ (prime p).asIdeal
    change quotientMap p (y p) ∈ primeIdeal p
    rw [primeIdeal_eq_span_y]
    exact Ideal.subset_span (Set.mem_singleton _)
  have hy_maximal : yP ∈ IsLocalRing.maximalIdeal P := by
    dsimp [yP]
    rw [← Localization.AtPrime.map_eq_maximalIdeal
      (I := (sourcePoint p).asIdeal)]
    exact Ideal.mem_map_of_mem _ hy_source
  have ha_maximal : a ∈ IsLocalRing.maximalIdeal P :=
    (IsLocalRing.maximalIdeal P).mul_mem_left _ hy_maximal
  have ha_zero : algebraMap P K a = 0 := by
    rw [IsScalarTower.algebraMap_apply P S K]
    have hlocal : IsLocalHom (localMap p).toRingHom := by
      unfold localMap
      infer_instance
    have htarget : (localMap p) a ∈ IsLocalRing.maximalIdeal S :=
      @map_nonunit P S _ _ _ _
        (localMap p).toRingHom hlocal a ha_maximal
    exact Ideal.Quotient.eq_zero_iff_mem.mpr htarget
  have hD :
      KaehlerDifferential.D (coeffField p) P (localizedEquation p) =
        a • KaehlerDifferential.D (coeffField p) P yP := by
    exact differential_localizedEquation (p := p) (T := P)
  have hx_map_zero :
      KaehlerDifferential.cotangentComplexBaseChange
          (coeffField p) S P K ((1 : K) ⊗ₜ[P] xKer) = 0 := by
    rw [KaehlerDifferential.cotangentComplexBaseChange_tmul, one_smul,
      KaehlerDifferential.kerToTensor_apply]
    rw [hD]
    have ha_one : a • (1 : K) = 0 := by
      rw [Algebra.smul_def, ha_zero, zero_mul]
    calc
      (1 : K) ⊗ₜ[P] (a • KaehlerDifferential.D (coeffField p) P yP) =
          (a • (1 : K)) ⊗ₜ[P]
            KaehlerDifferential.D (coeffField p) P yP :=
        TensorProduct.tmul_smul _ _ _
      _ = (0 : K) ⊗ₜ[P]
          KaehlerDifferential.D (coeffField p) P yP := by rw [ha_one]
      _ = 0 := TensorProduct.zero_tmul _ _
  have hx_zero : (1 : K) ⊗ₜ[P] xKer = 0 := by
    apply hinjective
    exact hx_map_zero
  have hresidue_surjective :
      Function.Surjective (algebraMap P K) :=
    residueField_algebraMap_surjective hsurjective
  have hx_ne : (1 : K) ⊗ₜ[P] xKer ≠ 0 := by
    intro hzero
    have hxmem : xKer ∈
        (RingHom.ker (algebraMap P K)) •
          (⊤ : Submodule P (RingHom.ker (algebraMap P S))) := by
      rw [← LinearMap.ker_tensorProductMk_of_surjective hresidue_surjective,
        LinearMap.mem_ker]
      exact hzero
    have h_under :
        localizedEquation p ∈ (RingHom.ker (algebraMap P K)) •
          (RingHom.ker (algebraMap P S) : Submodule P P) :=
      (Submodule.mem_smul_top_iff
        (I := RingHom.ker (algebraMap P K))
        (N := (RingHom.ker (algebraMap P S) : Submodule P P))
        (x := xKer)).mp hxmem
    rw [hker, Ideal.smul_eq_mul, Ideal.mem_mul_span_singleton] at h_under
    obtain ⟨z, hz, hzf⟩ := h_under
    have hmul : (1 - z) * localizedEquation p = 0 := by
      rw [sub_mul, one_mul, hzf, sub_self]
    have hz_one : z = 1 := by
      have hz_zero : 1 - z = 0 :=
        (mul_eq_zero.mp hmul).resolve_right hf_ne
      exact (sub_eq_zero.mp hz_zero).symm
    have hone_zero : (1 : K) = 0 := by
      rw [← map_one (algebraMap P K), ← hz_one]
      exact RingHom.mem_ker.mp hz
    exact one_ne_zero hone_zero
  exact hx_ne hx_zero

/-- Example 10.140.8 (3): if `2 < p`, the plane curve is not smooth at
`q = (y, x^p + t)`. -/
@[stacks 00TY "(3)"]
theorem not_isSmoothAt_of_two_lt (_h_two_lt : 2 < p) :
    ¬ IsSmoothAt (coeffField p) (prime p).asIdeal := by
  exact not_isSmoothAt p

/-- The bound-free core of Example 10.140.8 (4): the local ring of the plane
curve at `q = (y, x^p + t)` is regular. -/
theorem isRegularLocalRing :
    IsRegularLocalRing (Localization.AtPrime (prime p).asIdeal) := by
  apply IsLocalRing.PrincipalMaximalIdeal.isRegular_of_not_isArtinian
  · rw [local_maximalIdeal_eq_span_y]
    infer_instance
  · exact local_not_isArtinian p

/-- Example 10.140.8 (4): if `2 < p`, the local ring of the plane curve at
`q = (y, x^p + t)` is regular. -/
@[stacks 00TY "(4)"]
theorem isRegularLocalRing_of_two_lt (_h_two_lt : 2 < p) :
    IsRegularLocalRing (Localization.AtPrime (prime p).asIdeal) := by
  exact isRegularLocalRing p

#check @Ideal.Quotient.mkₐ
#check @MaximalSpectrum.toPrimeSpectrum
#check @PlaneCurve.quotientMap
#check @PlaneCurve.closedPoint

#print axioms PlaneCurve.quotientMap
#print axioms PlaneCurve.closedPoint
#print axioms NilpotentQuotient.kaehlerDifferential_free
#print axioms NilpotentQuotient.not_smooth
#print axioms PlaneCurve.not_isSmoothAt
#print axioms PlaneCurve.isRegularLocalRing

end PlaneCurve

end

end Algebra.CharP.Example_10_140_8
