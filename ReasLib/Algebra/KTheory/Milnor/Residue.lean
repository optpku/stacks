module

public import ReasLib.Algebra.KTheory.Milnor.Basic
public import ReasLib.RingTheory.LocalRing.TameSymbol.Determinant
public import ReasLib.RingTheory.LocalRing.TameSymbol.Factorization
public import ReasLib.RingTheory.Excellent
public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure
public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure.AtPrime
public import Mathlib.Algebra.BigOperators.Finprod

@[expose] public section

noncomputable section

open scoped BigOperators TensorProduct nonZeroDivisors

universe u v w

namespace MilnorK

/-- The tensor-level map induced by the tame symbol of a one-dimensional Noetherian local
domain. -/
def tameTensorBoundary
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) :
    (Additive Fˣ ⊗[ℤ] Additive Fˣ) →ₗ[ℤ]
      Additive ((IsLocalRing.ResidueField A)ˣ) :=
  TensorProduct.lift
    { toFun := fun x ↦
        { toFun := fun y ↦ Additive.ofMul
            (TameSymbol.value A F hdim (Additive.toMul x) (Additive.toMul y))
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }

/-- On a pure tensor, the tensor-level boundary is the concrete tame symbol. -/
theorem tameTensorBoundary_tmul
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) (x y : Fˣ) :
    tameTensorBoundary A F hdim (Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y) =
      Additive.ofMul (TameSymbol.value A F hdim x y) := sorry

/-- The tame symbol descends to an explicit homomorphism
`K₂ᴹ(F) → K₁ᴹ(IsLocalRing.ResidueField A)` in the tensor-quotient presentations. -/
def boundaryOne
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) :
    DegreeTwoPresentation F →ₗ[ℤ] Additive (IsLocalRing.ResidueField A)ˣ :=
  (degreeTwoRelations F).liftQ (tameTensorBoundary A F hdim) sorry

/-- On a pure degree-two symbol, `boundaryOne` is the local tame symbol. -/
theorem boundaryOne_tmul
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) (x y : Fˣ) :
    boundaryOne A F hdim
        (Submodule.Quotient.mk (Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y)) =
      Additive.ofMul (TameSymbol.value A F hdim x y) := sorry

/-- The divisor valuation of a fraction-field unit of a one-dimensional local domain. -/
noncomputable def divisorOrder
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) : Additive Fˣ →+ ℤ :=
  -- Local instance justification (proof-local temporary data): `hdim` supplies the bound required by `Ring.ordFrac`.
  letI : Ring.KrullDimLE 1 A :=
    (Ring.krullDimLE_iff).2 (hdim.le.trans_eq rfl)
  { toFun := fun a ↦ WithZero.log (Ring.ordFrac A ((Additive.toMul a : Fˣ) : F))
    map_zero' := sorry
    map_add' := sorry }

/-- A selected uniformizer used to present the explicit DVR symbol formula. -/
noncomputable def dvrUniformizer (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : A :=
  Classical.choose (IsDiscreteValuationRing.exists_irreducible A)

/-- The selected DVR uniformizer is irreducible. -/
theorem dvrUniformizer_irreducible (A : Type u) [CommRing A] [IsDomain A]
    [IsDiscreteValuationRing A] : Irreducible (dvrUniformizer A) := sorry

/-- The exponent and unit in the normal form of a fraction-field unit relative to a specified
uniformizer. -/
noncomputable def dvrNormalFormWith
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (π : A) (hπ : Irreducible π) (x : Fˣ) : ℤ × Aˣ :=
  let h := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hπ (Units.ne_zero x)
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h)⟩

/-- The normal-form exponent and unit recover the original fraction-field unit. -/
theorem dvrNormalFormWith_spec
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (π : A) (hπ : Irreducible π) (x : Fˣ) :
    (x : F) = (dvrNormalFormWith A F π hπ x).2 •
      algebraMap A F π ^ (dvrNormalFormWith A F π hπ x).1 := sorry

/-- The exponent and unit in the normal form relative to the selected DVR uniformizer. -/
noncomputable def dvrNormalForm
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (x : Fˣ) : ℤ × Aˣ :=
  dvrNormalFormWith A F (dvrUniformizer A)
    (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A)) x

/-- The normal-form exponent and unit recover the original fraction-field unit. -/
theorem dvrNormalForm_spec
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (x : Fˣ) :
    (x : F) = (dvrNormalForm A F x).2 •
      algebraMap A F (dvrUniformizer A) ^ (dvrNormalForm A F x).1 := sorry

/-- The residue of the unit part of the selected DVR normal form. -/
noncomputable def dvrResidueUnit
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (x : Fˣ) :
    (IsLocalRing.ResidueField A)ˣ :=
  Units.map (IsLocalRing.residue A).toMonoidHom (dvrNormalForm A F x).2

/-- The residue of the unit part of the normal form relative to a specified uniformizer. -/
noncomputable def dvrResidueUnitWith
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (π : A) (hπ : Irreducible π) (x : Fˣ) :
    (IsLocalRing.ResidueField A)ˣ :=
  Units.map (IsLocalRing.residue A).toMonoidHom (dvrNormalFormWith A F π hπ x).2

/-- The specified-uniformizer residue unit is obtained by reducing the unit part of its normal
form. -/
theorem dvrResidueUnitWith_apply
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (π : A) (hπ : Irreducible π) (x : Fˣ) :
    dvrResidueUnitWith A F π hπ x =
      Units.map (IsLocalRing.residue A).toMonoidHom (dvrNormalFormWith A F π hπ x).2 := sorry

/-- The higher tame-symbol formula on a pure tensor, presented using a specified uniformizer. -/
noncomputable def dvrSymbolFormulaWith
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (π : A) (hπ : Irreducible π) (i : ℕ) (x : Fin (i + 1) → Additive Fˣ) :
    Group i (IsLocalRing.ResidueField A) :=
  ∑ S : {S : Finset (Fin (i + 1)) // S.Nonempty},
    let p := S.1.max' S.2
    (((-1 : ℤ) ^ (i - p.1)) *
      ∏ r ∈ S.1, (dvrNormalFormWith A F π hπ (Additive.toMul (x r))).1) •
        symbol (fun s ↦
          if p.succAbove s ∈ S.1 then
            (-1 : (IsLocalRing.ResidueField A)ˣ)
          else dvrResidueUnitWith A F π hπ (Additive.toMul (x (p.succAbove s))))

/-- The specified-uniformizer symbol formula is independent of that uniformizer. -/
theorem dvrSymbolFormulaWith_eq
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (π ϖ : A) (hπ : Irreducible π) (hϖ : Irreducible ϖ)
    (i : ℕ) (x : Fin (i + 1) → Additive Fˣ) :
    dvrSymbolFormulaWith A F π hπ i x = dvrSymbolFormulaWith A F ϖ hϖ i x := sorry

/-- The higher tame-symbol formula on a pure `(i + 1)`-fold tensor.  The summand indexed by a
nonempty set `S` chooses the uniformizer term in exactly the positions in `S`; all but the last
such position become copies of `-1`.  Thus the terms with `S.card > 1` are precisely the sign
corrections omitted by the naive alternating valuation-residue formula. -/
noncomputable def dvrSymbolFormula
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (i : ℕ) (x : Fin (i + 1) → Additive Fˣ) :
    Group i (IsLocalRing.ResidueField A) :=
  dvrSymbolFormulaWith A F (dvrUniformizer A)
    (Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible A)) i x

/-- The corrected higher tame formula is multilinear in the Milnor-symbol entries. -/
noncomputable def dvrSymbolMultilinear
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (i : ℕ) :
    MultilinearMap ℤ (fun _ : Fin (i + 1) ↦ Additive Fˣ)
      (Group i (IsLocalRing.ResidueField A)) where
  toFun := dvrSymbolFormula A F i
  map_update_add' := sorry
  map_update_smul' := sorry

/-- The tensor-level higher tame boundary obtained from the corrected symbol formula. -/
noncomputable def dvrTensorBoundary
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (i : ℕ) :
    (⨂[ℤ] _ : Fin (i + 1), Additive Fˣ) →ₗ[ℤ]
      Group i (IsLocalRing.ResidueField A) :=
  PiTensorProduct.lift (dvrSymbolMultilinear A F i)

/-- Before passing to the Milnor quotient, the corrected higher tame formula kills every pure
tensor containing an adjacent Steinberg pair. -/
theorem dvrTensorBoundary_steinberg
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (i : ℕ) (x : Fin (i + 1) → Fˣ) (r : Fin i)
    (hxy : (x r.castSucc : F) + (x r.succ : F) = 1) :
    dvrTensorBoundary A F i
        (PiTensorProduct.tprod ℤ (fun s ↦ Additive.ofMul (x s))) = 0 := sorry

/-- The tensor-level higher tame boundary kills precisely the relations needed to descend to
the degree-`i + 1` Milnor K-group. -/
theorem dvrTensorBoundary_ker
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (i : ℕ) :
    LinearMap.ker (tensorToRing (i + 1) F) ≤ LinearMap.ker (dvrTensorBoundary A F i) := sorry

/-- The canonical higher tame boundary of a DVR, descended from its explicit formula on Milnor
symbols. -/
noncomputable def dvrBoundary
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (i : ℕ) :
    Group (i + 1) F →+ Group i (IsLocalRing.ResidueField A) :=
  (((LinearMap.ker (tensorToRing (i + 1) F)).liftQ
      (dvrTensorBoundary A F i) (dvrTensorBoundary_ker A F i)).comp
    ((LinearEquiv.ofEq _ _ (tensorToRing_range (i + 1) F)).symm.trans
      (tensorToRing (i + 1) F).quotKerEquivRange.symm).toLinearMap).toAddMonoidHom

/-- The canonical DVR boundary has the corrected higher tame-symbol value, including every
sign term arising from two or more uniformizer factors, on each pure Milnor symbol. -/
theorem dvrBoundary_symbol
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (i : ℕ) (x : Fin (i + 1) → Fˣ) :
    dvrBoundary A F i (symbol x) =
      dvrSymbolFormula A F i (fun r ↦ Additive.ofMul (x r)) := sorry

/-- The canonical DVR boundary is characterized by the same pure-symbol formula for every
choice of uniformizer. -/
theorem dvrBoundary_symbol_with_uniformizer
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (π : A) (hπ : Irreducible π) (i : ℕ) (x : Fin (i + 1) → Fˣ) :
    dvrBoundary A F i (symbol x) =
      dvrSymbolFormulaWith A F π hπ i (fun r ↦ Additive.ofMul (x r)) := sorry

/-- In degree one, the canonical higher DVR boundary is the concrete tame symbol. -/
theorem dvrBoundary_one
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (z : DegreeTwoPresentation F) :
    dvrBoundary A F 1 (degreeTwoMap F z) =
      degreeOneMap (IsLocalRing.ResidueField A)
        (boundaryOne A F (IsDiscreteValuationRing.ringKrullDim_eq_one A) z) := sorry

/-- On a degree-two pure symbol, the higher DVR boundary is exactly `TameSymbol.value` with
the sign convention used by the one-dimensional local theory. -/
theorem dvrBoundary_one_symbol
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (x y : Fˣ) :
    dvrBoundary A F 1 (symbol ![x, y]) =
      degreeOneMap (IsLocalRing.ResidueField A)
        (Additive.ofMul
          (TameSymbol.value A F (IsDiscreteValuationRing.ringKrullDim_eq_one A) x y)) := sorry

/-- In degree zero, the canonical DVR boundary is the divisor valuation. -/
theorem dvrBoundary_zero
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (a : Additive Fˣ) :
    dvrBoundary A F 0 (degreeOneMap F a) =
      degreeZeroMap (IsLocalRing.ResidueField A)
        (divisorOrder A F (IsDiscreteValuationRing.ringKrullDim_eq_one A) a) := sorry

/-- Maximal ideals of the normalization lying over the closed point of a local ring. -/
abbrev NormalizationBranch
    (A : Type u) (F : Type v) [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] :=
  {q : MaximalSpectrum (integralClosure A F) //
    q.asIdeal.LiesOver (IsLocalRing.maximalIdeal A)}

/-- Normalization branches are exactly maximal ideals of `integralClosure A F` lying over the
maximal ideal of `A`. -/
theorem normalizationBranch_def
    (A : Type u) (F : Type v) [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] :
    NormalizationBranch A F =
      {q : MaximalSpectrum (integralClosure A F) //
        q.asIdeal.LiesOver (IsLocalRing.maximalIdeal A)} := sorry

/-- The residue field attached to a branch of the normalization. -/
abbrev NormalizationBranch.ResidueField
    {A : Type u} {F : Type v} [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] (b : NormalizationBranch A F) :=
  b.1.asIdeal.ResidueField

/-- The degree-`i` Milnor group of a normalization branch residue field. -/
abbrev NormalizationBranch.Group
    {A : Type u} {F : Type v} [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] (i : ℕ) (b : NormalizationBranch A F) :=
  MilnorK.Group i b.ResidueField

/-- The degree-`i` Milnor group of the residue field of the local base. -/
abbrev LocalResidueGroup (A : Type u) [CommRing A] [IsLocalRing A] (i : ℕ) :=
  MilnorK.Group i (IsLocalRing.ResidueField A)

/-- Excellence makes the normalization of a domain in its fraction field finite over the
original domain. -/
instance normalizationFiniteOfExcellent
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsExcellentRing.{u, u} A]
    [Field F] [Algebra A F] [IsFractionRing A F] :
    Module.Finite A (integralClosure A F) := sorry

/-- The actual field norm on units of a normalization branch, transported to the canonical
residue-field model of the local base. -/
noncomputable def normalizationResidueNormOne
    (A : Type u) (F : Type v) [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] [Module.Finite A (integralClosure A F)]
    (b : NormalizationBranch A F) :
    Additive b.ResidueFieldˣ →+
      Additive (IsLocalRing.ResidueField A)ˣ where
  toFun a := Additive.ofMul <| Units.map
    (IsLocalRing.ResidueField.maximalIdealAlgEquiv A).symm.toMonoidHom
    (TameSymbol.residueNorm A b.1 b.2 (Additive.toMul a))
  map_zero' := sorry
  map_add' := sorry

/-- The fraction field `F` is canonically an algebra over the localization at a normalization
branch. -/
@[implicit_reducible]
noncomputable def normalizationBranchAlgebra
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field F] [Algebra A F] [IsFractionRing A F] (b : NormalizationBranch A F) :
    Algebra (Localization.AtPrime b.1.asIdeal) F :=
  IsLocalization.localizationAlgebraOfSubmonoidLe
    (Localization.AtPrime b.1.asIdeal) F b.1.asIdeal.primeCompl
      (nonZeroDivisors (integralClosure A F))
    b.1.asIdeal.primeCompl_le_nonZeroDivisors

/-- The localization at a normalization branch is an algebra in the given fraction field. -/
instance instAlgebraNormalizationBranch
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (b : NormalizationBranch A F) :
    Algebra (Localization.AtPrime b.1.asIdeal) F :=
  normalizationBranchAlgebra A F b

/-- The fraction field of the localization at a normalization branch is the original fraction
field `F`. -/
instance instIsFractionRingNormalizationBranch
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [Field F] [Algebra A F] [IsFractionRing A F]
    (b : NormalizationBranch A F) :
    IsFractionRing (Localization.AtPrime b.1.asIdeal) F := sorry

/-- In dimension one, a branch localization of the normalization is a discrete valuation
ring. -/
theorem normalizationBranchIsDiscreteValuationRing
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) (b : NormalizationBranch A F) :
    IsDiscreteValuationRing (Localization.AtPrime b.1.asIdeal) := sorry

/-- The canonical higher tame boundary at a branch of the normalization. -/
noncomputable def normalizationBranchBoundary
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) (b : NormalizationBranch A F) (i : ℕ) :
    Group (i + 1) F →+ b.Group i :=
  -- Local instance justification (proof-local temporary data): the explicit dimension-one proof hdim makes this selected normalization branch a DVR; install that property only while applying dvrBoundary.
  letI : IsDiscreteValuationRing (Localization.AtPrime b.1.asIdeal) :=
    normalizationBranchIsDiscreteValuationRing A F hdim b
  dvrBoundary (Localization.AtPrime b.1.asIdeal) F i

/-- A graded transfer in Milnor K-theory along a finite field map.  Besides its maps in every
degree, the interface records the degree-zero degree, the ordinary field norm in degree one,
and the projection formula on pure symbols in all bidegrees. -/
structure GradedTransfer
    (k : Type u) (L : Type v) [Field k] [Field L]
    (scalarMap : k →+* L) (extensionDegree : ℕ)
    (normOne : Additive Lˣ →+ Additive kˣ) where
  map : (i : ℕ) → Group i L →+ Group i k
  degreeZero_apply : ∀ z : ℤ,
    map 0 (degreeZeroMap L z) = degreeZeroMap k ((extensionDegree : ℤ) * z)
  degreeOne_apply : ∀ a : Additive Lˣ,
    map 1 (degreeOneMap L a) = degreeOneMap k (normOne a)
  projection_formula_symbols : ∀ (p q : ℕ) (a : Fin p → kˣ) (b : Fin q → Lˣ),
    ((map (p + q) (symbol (Fin.addCases
      (fun r ↦ Units.map scalarMap.toMonoidHom (a r)) b)) : Group (p + q) k) : Ring k) =
        (symbol a : Ring k) * (map q (symbol b) : Ring k)

namespace GradedTransfer

/-- Build a graded Milnor transfer from its maps, degree-zero and degree-one normalizations,
and its projection formula in every bidegree. -/
def ofMaps
    {k : Type u} {L : Type v} [Field k] [Field L]
    {scalarMap : k →+* L} {extensionDegree : ℕ}
    {normOne : Additive Lˣ →+ Additive kˣ}
    (map : (i : ℕ) → Group i L →+ Group i k)
    (degreeZero_apply : ∀ z : ℤ,
      map 0 (degreeZeroMap L z) = degreeZeroMap k ((extensionDegree : ℤ) * z))
    (degreeOne_apply : ∀ a : Additive Lˣ,
      map 1 (degreeOneMap L a) = degreeOneMap k (normOne a))
    (projection_formula_symbols : ∀ (p q : ℕ) (a : Fin p → kˣ) (b : Fin q → Lˣ),
      ((map (p + q) (symbol (Fin.addCases
        (fun r ↦ Units.map scalarMap.toMonoidHom (a r)) b)) : Group (p + q) k) : Ring k) =
          (symbol a : Ring k) * (map q (symbol b) : Ring k)) :
    GradedTransfer k L scalarMap extensionDegree normOne where
  map := map
  degreeZero_apply := degreeZero_apply
  degreeOne_apply := degreeOne_apply
  projection_formula_symbols := projection_formula_symbols

/-- The degree-zero member of a graded transfer is multiplication by the field-extension
degree. -/
theorem map_zero_apply
    {k : Type u} {L : Type v} [Field k] [Field L]
    {scalarMap : k →+* L} {extensionDegree : ℕ}
    {normOne : Additive Lˣ →+ Additive kˣ}
    (T : GradedTransfer k L scalarMap extensionDegree normOne) (z : ℤ) :
    T.map 0 (degreeZeroMap L z) = degreeZeroMap k ((extensionDegree : ℤ) * z) := sorry

/-- The degree-one member of a graded Milnor transfer is its specified field norm on units. -/
theorem map_one_apply
    {k : Type u} {L : Type v} [Field k] [Field L]
    {scalarMap : k →+* L} {extensionDegree : ℕ}
    {normOne : Additive Lˣ →+ Additive kˣ}
    (T : GradedTransfer k L scalarMap extensionDegree normOne)
    (a : Additive Lˣ) :
    T.map 1 (degreeOneMap L a) = degreeOneMap k (normOne a) := sorry

end GradedTransfer

/-- A normalization branch lies over the closed point of the local base. -/
instance instLiesOverNormalizationBranch
    {A : Type u} {F : Type v} [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] (b : NormalizationBranch A F) :
    b.1.asIdeal.LiesOver (IsLocalRing.maximalIdeal A) :=
  b.2

/-- The residue-field algebra of a normalization branch along the closed point. -/
instance instAlgebraResidueNormalizationBranch
    {A : Type u} {F : Type v} [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] (b : NormalizationBranch A F) :
    Algebra (IsLocalRing.maximalIdeal A).ResidueField b.ResidueField :=
  Ideal.ResidueField.algebraOfLiesOver (IsLocalRing.maximalIdeal A) b.1.asIdeal

/-- The canonical residue-field map from the closed point of a local ring to a branch of its
normalization. -/
noncomputable def normalizationResidueMap
    (A : Type u) (F : Type v) [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] (b : NormalizationBranch A F) :
    IsLocalRing.ResidueField A →+* b.ResidueField :=
  (algebraMap (IsLocalRing.maximalIdeal A).ResidueField b.ResidueField).comp
    (IsLocalRing.ResidueField.maximalIdealAlgEquiv A).toRingHom

/-- The finite degree of the residue-field extension attached to a normalization branch. -/
noncomputable def normalizationResidueDegree
    (A : Type u) (F : Type v) [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] (b : NormalizationBranch A F) : ℕ :=
  Module.finrank (IsLocalRing.maximalIdeal A).ResidueField b.ResidueField

/-- The graded Milnor transfer along the actual finite residue-field extension attached to a
normalization branch. -/
abbrev NormalizationResidueTransfer
    (A : Type u) (F : Type v) [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] [Module.Finite A (integralClosure A F)]
    (b : NormalizationBranch A F) :=
  GradedTransfer (IsLocalRing.ResidueField A) b.ResidueField
    (normalizationResidueMap A F b) (normalizationResidueDegree A F b)
    (normalizationResidueNormOne A F b)

namespace NormalizationResidueTransfer

/-- The degree-one member of a normalization residue transfer is the actual residue-field norm. -/
theorem map_one_apply
    {A : Type u} {F : Type v} [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] [Module.Finite A (integralClosure A F)]
    {b : NormalizationBranch A F}
    (N : NormalizationResidueTransfer A F b)
    (a : Additive b.1.asIdeal.ResidueFieldˣ) :
    N.map 1 (degreeOneMap b.1.asIdeal.ResidueField a) =
      degreeOneMap (IsLocalRing.ResidueField A) (normalizationResidueNormOne A F b a) := sorry

end NormalizationResidueTransfer

/-- The excellent-local boundary obtained by summing the canonical branch DVR boundaries followed
by the graded Milnor transfers of the actual residue-field extensions. -/
noncomputable def excellentLocalBoundary
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1)
    (N : (b : NormalizationBranch A F) → NormalizationResidueTransfer A F b) (i : ℕ) :
    Group (i + 1) F →+ Group i (IsLocalRing.ResidueField A) where
  toFun a := ∑ᶠ b, (N b).map i (normalizationBranchBoundary A F hdim b i a)
  map_zero' := sorry
  map_add' := sorry

/-- The excellent-local boundary is the finite sum of the canonical branch DVR boundaries
followed by the corresponding graded residue-field transfers. -/
theorem excellentLocalBoundary_apply
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1)
    (N : (b : NormalizationBranch A F) → NormalizationResidueTransfer A F b)
    (i : ℕ) (a : Group (i + 1) F) :
    excellentLocalBoundary A F hdim N i a =
      ∑ᶠ b, (N b).map i (normalizationBranchBoundary A F hdim b i a) := sorry

/-- In degree one, the normalization-and-transfer construction agrees with the concrete tame symbol
of the original one-dimensional local domain. -/
theorem excellentLocalBoundary_one
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1)
    (N : (b : NormalizationBranch A F) → NormalizationResidueTransfer A F b)
    (z : DegreeTwoPresentation F) :
    excellentLocalBoundary A F hdim N 1 (degreeTwoMap F z) =
      degreeOneMap (IsLocalRing.ResidueField A) (boundaryOne A F hdim z) := sorry

/-- In degree zero, the normalization-and-transfer boundary agrees with the divisor valuation
of the original excellent local domain. -/
theorem excellentLocalBoundary_zero
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsExcellentRing.{u, u} A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1)
    (N : (b : NormalizationBranch A F) → NormalizationResidueTransfer A F b)
    (a : Additive Fˣ) :
    excellentLocalBoundary A F hdim N 0 (degreeOneMap F a) =
      degreeZeroMap (IsLocalRing.ResidueField A) (divisorOrder A F hdim a) := sorry


/-- The degree-two tame symbol, rewritten as a map on `K₂ᴹ(F)`. -/
noncomputable def boundaryOneOnGroup
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) :
    Group 2 F →+ Group 1 (IsLocalRing.ResidueField A) :=
  (degreeOneMap (IsLocalRing.ResidueField A)).comp
    ((boundaryOne A F hdim).toAddMonoidHom.comp (degreeTwoEquiv F).symm.toAddMonoidHom)

/-- On a pure degree-two symbol, `boundaryOneOnGroup` is the local tame symbol. -/
theorem boundaryOneOnGroup_symbol
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) (x y : Fˣ) :
    boundaryOneOnGroup A F hdim (symbol ![x, y]) =
      degreeOneMap (IsLocalRing.ResidueField A)
        (Additive.ofMul (TameSymbol.value A F hdim x y)) := sorry

/-- The divisor valuation, rewritten as a map on `K₁ᴹ(F)`. -/
noncomputable def divisorOrderOnGroup
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) :
    Group 1 F →+ Group 0 (IsLocalRing.ResidueField A) :=
  (degreeZeroMap (IsLocalRing.ResidueField A)).comp
    ((divisorOrder A F hdim).comp (degreeOneEquiv F).symm.toAddMonoidHom)

/-- On a degree-one generator, `divisorOrderOnGroup` is the divisor valuation. -/
theorem divisorOrderOnGroup_degreeOne
    (A : Type u) (F : Type v) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Field F] [Algebra A F] [IsFractionRing A F]
    (hdim : ringKrullDim A = 1) (a : Additive Fˣ) :
    divisorOrderOnGroup A F hdim (degreeOneMap F a) =
      degreeZeroMap (IsLocalRing.ResidueField A) (divisorOrder A F hdim a) := sorry

end MilnorK
