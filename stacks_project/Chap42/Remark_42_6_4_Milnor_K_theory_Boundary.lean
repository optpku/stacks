/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap42.Definition_42_68_31_TameSymbol
public import stacks_project.Chap42.Remark_42_6_4_Milnor_K_theory_MilnorK
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Algebra.DirectSum.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.RingTheory.Excellent
public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure
public import ReasLib.RingTheory.Localization.FractionRing.IntegralClosure.AtPrime
public import ReasLib.RingTheory.Localization.AtPrime.FractionRing
public import ReasLib.Topology.Specialization.Dimension
public import stacks_project.Chap42.«42_5_0_1_TameSymbol»
public import stacks_project.Chap42.Lemma_42_6_3_Key_Lemma

@[expose] public section

noncomputable section

open scoped BigOperators TensorProduct nonZeroDivisors

universe u v w

namespace MilnorK

/-- The canonical map from `ℤ` to the degree-zero Milnor K-group. -/
def degreeZeroMap (k : Type u) [Field k] : ℤ →+ Group 0 k where
  toFun n := ⟨quotientMk k (algebraMap ℤ (TensorAlgebra ℤ (Additive kˣ)) n), sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- The canonical degree-zero map identifies `ℤ` with `K₀ᴹ(k)`. -/
theorem degreeZeroMap_bijective (k : Type u) [Field k] :
    Function.Bijective (degreeZeroMap k) := sorry

/-- The canonical map from the additive form of `kˣ` to the degree-one Milnor K-group. -/
def degreeOneMap (k : Type u) [Field k] : Additive kˣ →+ Group 1 k where
  toFun x := ⟨quotientMk k (TensorAlgebra.ι ℤ x), sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- The canonical degree-one map identifies `Additive kˣ` with `K₁ᴹ(k)`. -/
theorem degreeOneMap_bijective (k : Type u) [Field k] :
    Function.Bijective (degreeOneMap k) := sorry

/-- The degree-two Steinberg relations inside `Additive kˣ ⊗[ℤ] Additive kˣ`. -/
def degreeTwoRelations (k : Type u) [Field k] :
    Submodule ℤ (Additive kˣ ⊗[ℤ] Additive kˣ) :=
  Submodule.span ℤ {z | ∃ x y : kˣ, (x : k) + (y : k) = 1 ∧
    z = Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y}

/-- Membership in the degree-two relation submodule is membership in the span of the
Steinberg tensors. -/
theorem mem_degreeTwoRelations_iff {k : Type u} [Field k]
    {z : Additive kˣ ⊗[ℤ] Additive kˣ} :
    z ∈ degreeTwoRelations k ↔ z ∈ Submodule.span ℤ
      {w | ∃ x y : kˣ, (x : k) + (y : k) = 1 ∧
        w = Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y} := sorry

/-- The tensor-product presentation of `K₂ᴹ(k)`. -/
abbrev DegreeTwoPresentation (k : Type u) [Field k] :=
  (Additive kˣ ⊗[ℤ] Additive kˣ) ⧸ degreeTwoRelations k

/-- The bilinear symbol map from the degree-two tensor product into `K₂ᴹ(k)`. -/
def degreeTwoTensorMap (k : Type u) [Field k] :
    (Additive kˣ ⊗[ℤ] Additive kˣ) →ₗ[ℤ] Group 2 k :=
  TensorProduct.lift
    { toFun := fun x ↦
        { toFun := fun y ↦
            ⟨quotientMk k
              (TensorAlgebra.ι ℤ x * TensorAlgebra.ι ℤ y), sorry⟩
          map_add' := sorry
          map_smul' := sorry }
      map_add' := sorry
      map_smul' := sorry }

/-- A pure tensor maps to the product of its two degree-one generators. -/
theorem degreeTwoTensorMap_tmul (k : Type u) [Field k] (x y : kˣ) :
    (degreeTwoTensorMap k
      (Additive.ofMul x ⊗ₜ[ℤ] Additive.ofMul y) : Ring k) =
        quotientMk k
          (TensorAlgebra.ι ℤ (Additive.ofMul x) *
            TensorAlgebra.ι ℤ (Additive.ofMul y)) := sorry

/-- The canonical map from the Steinberg quotient presentation into `K₂ᴹ(k)`. -/
def degreeTwoMap (k : Type u) [Field k] :
    DegreeTwoPresentation k →ₗ[ℤ] Group 2 k :=
  (degreeTwoRelations k).liftQ (degreeTwoTensorMap k) sorry

/-- The Steinberg quotient presentation identifies canonically with `K₂ᴹ(k)`. -/
theorem degreeTwoMap_bijective (k : Type u) [Field k] :
    Function.Bijective (degreeTwoMap k) := sorry

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

/-- The tensor-power map whose range is the degree-`n` Milnor K-group. -/
def tensorToRing (n : ℕ) (k : Type u) [Field k] :
    (⨂[ℤ]^n (Additive kˣ)) →ₗ[ℤ] Ring k :=
  (quotientMk k).toIntAlgHom.toLinearMap.comp
    (TensorPower.toTensorAlgebra :
      (⨂[ℤ]^n (Additive kˣ)) →ₗ[ℤ] TensorAlgebra ℤ (Additive kˣ))

/-- The range of `tensorToRing` is the degree-`n` Milnor K-group. -/
theorem tensorToRing_range (n : ℕ) (k : Type u) [Field k] :
    LinearMap.range (tensorToRing n k) = degree n k := sorry

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
  -- Local instance justification (proof-local temporary data): excellence and dimension one
  -- make this normalization branch a DVR, which is not inferable from the localization alone.
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

/-- Build the normalization residue transfer from maps satisfying its defining laws in every
degree. -/
def ofMaps
    {A : Type u} {F : Type v} [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] [Module.Finite A (integralClosure A F)]
    {b : NormalizationBranch A F}
    (map : (i : ℕ) → Group i b.1.asIdeal.ResidueField →+
      Group i (IsLocalRing.ResidueField A))
    (degreeZero_apply : ∀ z : ℤ,
      map 0 (degreeZeroMap b.ResidueField z) =
        degreeZeroMap (IsLocalRing.ResidueField A)
          ((normalizationResidueDegree A F b : ℤ) * z))
    (degreeOne_apply : ∀ a : Additive b.1.asIdeal.ResidueFieldˣ,
      map 1 (degreeOneMap b.1.asIdeal.ResidueField a) =
        degreeOneMap (IsLocalRing.ResidueField A) (normalizationResidueNormOne A F b a))
    (projection_formula_symbols : ∀ (p q : ℕ)
      (a : Fin p → (IsLocalRing.ResidueField A)ˣ) (c : Fin q → b.ResidueFieldˣ),
      ((map (p + q) (symbol (Fin.addCases
        (fun r ↦ Units.map (normalizationResidueMap A F b).toMonoidHom (a r)) c)) :
          Group (p + q) (IsLocalRing.ResidueField A)) : Ring (IsLocalRing.ResidueField A)) =
        (symbol a : Ring (IsLocalRing.ResidueField A)) *
          (map q (symbol c) : Ring (IsLocalRing.ResidueField A))) :
    NormalizationResidueTransfer A F b :=
  GradedTransfer.ofMaps map degreeZero_apply degreeOne_apply projection_formula_symbols

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

/-- Compatibility spelling for the normalization-residue transfer. Its value is the full graded
transfer interface, not merely a degree-one norm. -/
abbrev NormalizationResidueNorm
    (A : Type u) (F : Type v) [CommRing A] [IsLocalRing A]
    [Field F] [Algebra A F] [Module.Finite A (integralClosure A F)]
    (b : NormalizationBranch A F) :=
  NormalizationResidueTransfer A F b

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


/-- The additive map on units induced by a homomorphism of fields. -/
def unitsHomAdditive {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L) :
    Additive kˣ →+ Additive Lˣ where
  toFun x := Additive.ofMul (Units.map f.toMonoidHom (Additive.toMul x))
  map_zero' := sorry
  map_add' := sorry

/-- The tensor-algebra map induced by a homomorphism of fields. -/
def tensorAlgebraMap {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L) :
    TensorAlgebra ℤ (Additive kˣ) →ₐ[ℤ] TensorAlgebra ℤ (Additive Lˣ) :=
  TensorAlgebra.lift ℤ <|
    (TensorAlgebra.ι ℤ).comp (unitsHomAdditive f).toIntLinearMap

/-- The induced map of Milnor K-rings along a homomorphism of fields. -/
def mapRing {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L) :
    Ring k →+* Ring L :=
  (steinbergIdeal k).ringCon.lift ((quotientMk L).comp (tensorAlgebraMap f).toRingHom) sorry

/-- Applying `mapRing` recovers the image of a tensor-algebra element. -/
theorem mapRing_quotientMk {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L)
    (z : TensorAlgebra ℤ (Additive kˣ)) :
    mapRing f (quotientMk k z) = quotientMk L (tensorAlgebraMap f z) := sorry

/-- The induced map of degree-`n` Milnor K-groups along a homomorphism of fields. -/
def mapGroup {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L) (n : ℕ) :
    Group n k →+ Group n L where
  toFun a := ⟨mapRing f a.1, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- A pure symbol is sent to the symbol of the image units. -/
theorem mapGroup_symbol {k : Type u} {L : Type v} [Field k] [Field L] (f : k →+* L)
    {n : ℕ} (a : Fin n → kˣ) :
    mapGroup f n (symbol a) =
      symbol (fun r ↦ Units.map f.toMonoidHom (a r)) := sorry

/-- The canonical identification of `Additive kˣ` with `K₁ᴹ(k)`. -/
noncomputable def degreeOneEquiv (k : Type u) [Field k] :
    Additive kˣ ≃+ Group 1 k :=
  AddEquiv.ofBijective (degreeOneMap k) (degreeOneMap_bijective k)

/-- The canonical identification of the Steinberg presentation with `K₂ᴹ(k)`. -/
noncomputable def degreeTwoEquiv (k : Type u) [Field k] :
    DegreeTwoPresentation k ≃+ Group 2 k :=
  AddEquiv.ofBijective (degreeTwoMap k).toAddMonoidHom (degreeTwoMap_bijective k)

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

open AlgebraicGeometry
open scoped DirectSum
open Classical

namespace MilnorK.Coniveau

/-- The canonical map from the stalk at a specialization point to the residue field at its
generization. -/
def specializationToResidue {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    X.presheaf.stalk y →+* X.residueField x :=
  (X.residue x).hom.comp (X.presheaf.stalkSpecializes h).hom

/-- The canonical one-dimensional local domain attached to a specialization `x ⤳ y`: the
stalk at `y`, modulo the kernel of its map to `κ(x)`. -/
abbrev SpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :=
  X.presheaf.stalk y ⧸ RingHom.ker (specializationToResidue h)

/-- The specialization quotient is an algebra in the residue field of the generization. -/
instance instAlgebraSpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    Algebra (SpecializationLocalRing h) (X.residueField x) :=
  (Ideal.Quotient.lift (RingHom.ker (specializationToResidue h))
    (specializationToResidue h) fun _ ha ↦ ha).toAlgebra

/-- A scheme whose stalks are excellent rings. -/
class StalkwiseExcellent (X : Scheme.{u}) : Prop where
  /-- Every stalk is an excellent ring. -/
  stalk : ∀ x : X, IsExcellentRing.{u, u} (X.presheaf.stalk x)

/-- Stalks of a stalkwise excellent scheme are excellent rings. -/
instance instIsExcellentRing_stalk {X : Scheme.{u}} [StalkwiseExcellent X] (x : X) :
    IsExcellentRing.{u, u} (X.presheaf.stalk x) :=
  StalkwiseExcellent.stalk x

/-- The spectrum of a field is stalkwise excellent. -/
instance instStalkwiseExcellent_spec_field (k : Type u) [Field k] :
    StalkwiseExcellent (Spec (.of k)) := sorry

/-- A specialization quotient is a domain. -/
instance instIsDomainSpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    IsDomain (SpecializationLocalRing h) := sorry

/-- A specialization quotient is local. -/
instance instIsLocalRingSpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    IsLocalRing (SpecializationLocalRing h) := sorry

/-- On a Noetherian scheme, a specialization quotient is Noetherian. -/
instance instIsNoetherianRingSpecializationLocalRing
    {X : Scheme.{u}} [IsNoetherian X] {x y : X} (h : x ⤳ y) :
    IsNoetherianRing (SpecializationLocalRing h) := sorry

/-- The residue field of the generization is the fraction field of the specialization
quotient. -/
instance instIsFractionRingSpecializationLocalRing {X : Scheme.{u}} {x y : X} (h : x ⤳ y) :
    IsFractionRing (SpecializationLocalRing h) (X.residueField x) := sorry

/-- Stalkwise excellence makes a specialization quotient excellent. -/
instance instIsExcellentRingSpecializationLocalRing {X : Scheme.{u}} {x y : X}
    [IsExcellentRing.{u, u} (X.presheaf.stalk y)] (h : x ⤳ y) :
    IsExcellentRing.{u, u} (SpecializationLocalRing h) := sorry

/-- An immediate specialization has local dimension one. -/
theorem specializationDimension_eq_one {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    ringKrullDim (SpecializationLocalRing hxy.specializes) = 1 := sorry

/-- The residue map of an immediate specialization quotient toward `κ(y)`. -/
noncomputable def specializationResidueHom {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    SpecializationLocalRing hxy.specializes →+* X.residueField y :=
  Ideal.Quotient.lift (RingHom.ker (specializationToResidue hxy.specializes))
    (X.residue y).hom sorry

/-- The residue map of an immediate specialization quotient is local. -/
instance instIsLocalHomSpecializationResidueHom {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    IsLocalHom (specializationResidueHom hxy) := sorry

/-- The induced map of residue fields identifying the specialization quotient with `κ(y)`. -/
noncomputable def specializationResidueFieldMap {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    IsLocalRing.ResidueField (SpecializationLocalRing hxy.specializes) →+*
      X.residueField y :=
  IsLocalRing.ResidueField.lift (specializationResidueHom hxy)

/-- The residue-field map of an immediate specialization is bijective. -/
theorem specializationResidueFieldMap_bijective {X : Scheme.{u}} {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    Function.Bijective (specializationResidueFieldMap hxy) := sorry

/-- Branchwise higher Milnor transfers along residue extensions of immediate specializations
of an excellent Noetherian scheme. -/
abbrev SpecializationTransfers (X : Scheme.{u}) [IsNoetherian X]
    [StalkwiseExcellent X] :=
  ∀ {x y : X} (hxy : IsImmediateSpecialization x y),
    (b : NormalizationBranch (SpecializationLocalRing hxy.specializes) (X.residueField x)) →
      NormalizationResidueTransfer (SpecializationLocalRing hxy.specializes)
        (X.residueField x) b

/-- The Milnor K-group direct sum over the points of dimension `j`. -/
abbrev Term (X : Scheme.{u}) (δ : X → ℤ) (i : ℕ) (j : ℤ) :=
  ⨁ x : {x : X // δ x = j}, Group i (X.residueField x.1)

/-- The coniveau term is the direct sum of the indicated residue-field Milnor K-groups. -/
theorem term_def (X : Scheme.{u}) (δ : X → ℤ) (i : ℕ) (j : ℤ) :
    Term X δ i j = (⨁ x : {x : X // δ x = j}, Group i (X.residueField x.1)) := sorry

/-- The canonical inclusion of one residue-field summand into a coniveau term. -/
noncomputable def termOf {X : Scheme.{u}} {δ : X → ℤ} {i : ℕ} {j : ℤ}
    (x : {x : X // δ x = j}) :
    Group i (X.residueField x.1) →+ Term X δ i j :=
  @DirectSum.of _ (fun y : {y : X // δ y = j} ↦ Group i (X.residueField y.1)) _
    (Classical.decEq _) x

/-- Evaluating the canonical summand inclusion at its own index recovers the original class. -/
theorem termOf_eq_same {X : Scheme.{u}} {δ : X → ℤ} {i : ℕ} {j : ℤ}
    (x : {x : X // δ x = j}) (a : Group i (X.residueField x.1)) :
    termOf x a x = a := sorry

/-- The excellent local residue `Kᵐ_{i+1}(κ(x)) →+ Kᵐ_i(κ(y))` along an immediate
specialization, using the supplied branchwise transfers. -/
noncomputable def excellentResidue {X : Scheme.{u}} [IsNoetherian X]
    [StalkwiseExcellent X] {x y : X}
    (hxy : IsImmediateSpecialization x y)
    (N : (b : NormalizationBranch (SpecializationLocalRing hxy.specializes) (X.residueField x)) →
      NormalizationResidueTransfer (SpecializationLocalRing hxy.specializes)
        (X.residueField x) b)
    (i : ℕ) :
    Group (i + 1) (X.residueField x) →+ Group i (X.residueField y) :=
  (mapGroup (specializationResidueFieldMap hxy) i).comp
    (excellentLocalBoundary (SpecializationLocalRing hxy.specializes)
      (X.residueField x) (specializationDimension_eq_one hxy) N i)

/-- The preceding-degree excellent residue along the same immediate specialization. -/
noncomputable def excellentResiduePrev {X : Scheme.{u}} [IsNoetherian X]
    [StalkwiseExcellent X] {x y : X}
    (hxy : IsImmediateSpecialization x y)
    (N : (b : NormalizationBranch (SpecializationLocalRing hxy.specializes) (X.residueField x)) →
      NormalizationResidueTransfer (SpecializationLocalRing hxy.specializes)
        (X.residueField x) b)
    (i : ℕ) (hi : 1 ≤ i) :
    Group i (X.residueField x) →+ Group (i - 1) (X.residueField y) :=
  (Nat.sub_add_cancel hi).symm ▸ excellentResidue hxy N (i - 1)

/-- Local components of the first excellent coniveau arrow: the excellent residue on incident
pairs, and zero otherwise. -/
noncomputable def excellentFirstLocal {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [StalkwiseExcellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1}) (y : {y : X // δ y = j}) :
    Group (i + 1) (X.residueField x.1) →+ Group i (X.residueField y.1) :=
  if hxy : IsImmediateSpecialization x.1 y.1 then
    excellentResidue hxy (transfers hxy) i
  else
    0

/-- Local components of the second excellent coniveau arrow. -/
noncomputable def excellentSecondLocal {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [StalkwiseExcellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j}) (y : {y : X // δ y = j - 1}) :
    Group i (X.residueField x.1) →+ Group (i - 1) (X.residueField y.1) :=
  if hxy : IsImmediateSpecialization x.1 y.1 then
    excellentResiduePrev hxy (transfers hxy) i hi
  else
    0

/-- On an immediate specialization, the first local component is the excellent residue. -/
theorem excellentFirstLocal_of_isImmediate {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [StalkwiseExcellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1}) (y : {y : X // δ y = j})
    (hxy : IsImmediateSpecialization x.1 y.1) :
    excellentFirstLocal δ transfers i j x y =
      excellentResidue hxy (transfers hxy) i := sorry

/-- On an immediate specialization, the second local component is the preceding excellent
residue. -/
theorem excellentSecondLocal_of_isImmediate {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [StalkwiseExcellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j}) (y : {y : X // δ y = j - 1})
    (hxy : IsImmediateSpecialization x.1 y.1) :
    excellentSecondLocal δ transfers i hi j x y =
      excellentResiduePrev hxy (transfers hxy) i hi := sorry

/-- The first displayed excellent coniveau arrow. -/
noncomputable def excellentFirst {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [StalkwiseExcellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ) :
    Term X δ (i + 1) (j + 1) →+ Term X δ i j :=
  @DirectSum.toAddMonoid _ _ _ (Classical.decEq _) _ _
    fun x ↦
      { toFun a := ∑ᶠ y, termOf y (excellentFirstLocal δ transfers i j x y a)
        map_zero' := sorry
        map_add' := sorry }

/-- The second displayed excellent coniveau arrow. -/
noncomputable def excellentSecond {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [StalkwiseExcellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ) :
    Term X δ i j →+ Term X δ (i - 1) (j - 1) :=
  @DirectSum.toAddMonoid _ _ _ (Classical.decEq _) _ _
    fun x ↦
      { toFun a := ∑ᶠ y, termOf y (excellentSecondLocal δ transfers i hi j x y a)
        map_zero' := sorry
        map_add' := sorry }

/-- Evaluating the first excellent arrow on a homogeneous summand is the corresponding local
residue sum. -/
theorem excellentFirst_of {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [StalkwiseExcellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (j : ℤ)
    (x : {x : X // δ x = j + 1}) (a : Group (i + 1) (X.residueField x.1)) :
    excellentFirst δ transfers i j (termOf x a) =
      ∑ᶠ y, termOf y (excellentFirstLocal δ transfers i j x y a) := sorry

/-- Evaluating the second excellent arrow on a homogeneous summand is the corresponding local
residue sum. -/
theorem excellentSecond_of {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ]
    [StalkwiseExcellent X]
    (transfers : SpecializationTransfers X) (i : ℕ) (hi : 1 ≤ i) (j : ℤ)
    (x : {x : X // δ x = j}) (a : Group i (X.residueField x.1)) :
    excellentSecond δ transfers i hi j (termOf x a) =
      ∑ᶠ y, termOf y (excellentSecondLocal δ transfers i hi j x y a) := sorry

/-- The degree-one residue along an immediate specialization, using the concrete tame symbol. -/
noncomputable def degreeOneResidue {X : Scheme.{u}} [IsNoetherian X] {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    Group 2 (X.residueField x) →+ Group 1 (X.residueField y) :=
  (mapGroup (specializationResidueFieldMap hxy) 1).comp
    (boundaryOneOnGroup (SpecializationLocalRing hxy.specializes)
      (X.residueField x) (specializationDimension_eq_one hxy))

/-- The degree-zero residue along an immediate specialization, using the divisor valuation. -/
noncomputable def degreeZeroResidue {X : Scheme.{u}} [IsNoetherian X] {x y : X}
    (hxy : IsImmediateSpecialization x y) :
    Group 1 (X.residueField x) →+ Group 0 (X.residueField y) :=
  (mapGroup (specializationResidueFieldMap hxy) 0).comp
    (divisorOrderOnGroup (SpecializationLocalRing hxy.specializes)
      (X.residueField x) (specializationDimension_eq_one hxy))

/-- Local components of the first degree-one coniveau arrow. -/
noncomputable def degreeOneFirstLocal {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j + 1}) (y : {y : X // δ y = j}) :
    Group 2 (X.residueField x.1) →+ Group 1 (X.residueField y.1) :=
  if hxy : IsImmediateSpecialization x.1 y.1 then degreeOneResidue hxy else 0

/-- Local components of the second degree-one coniveau arrow. -/
noncomputable def degreeOneSecondLocal {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j}) (y : {y : X // δ y = j - 1}) :
    Group 1 (X.residueField x.1) →+ Group 0 (X.residueField y.1) :=
  if hxy : IsImmediateSpecialization x.1 y.1 then degreeZeroResidue hxy else 0

/-- On an immediate specialization, the first degree-one local component is the tame symbol. -/
theorem degreeOneFirstLocal_of_isImmediate {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j + 1}) (y : {y : X // δ y = j})
    (hxy : IsImmediateSpecialization x.1 y.1) :
    degreeOneFirstLocal δ j x y = degreeOneResidue hxy := sorry

/-- On an immediate specialization, the second degree-one local component is the divisor
order. -/
theorem degreeOneSecondLocal_of_isImmediate {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j}) (y : {y : X // δ y = j - 1})
    (hxy : IsImmediateSpecialization x.1 y.1) :
    degreeOneSecondLocal δ j x y = degreeZeroResidue hxy := sorry

/-- The first degree-one coniveau arrow, assembled from local tame symbols. -/
noncomputable def degreeOneFirst {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ) :
    Term X δ 2 (j + 1) →+ Term X δ 1 j :=
  @DirectSum.toAddMonoid _ _ _ (Classical.decEq _) _ _
    fun x ↦
      { toFun a := ∑ᶠ y, termOf y (degreeOneFirstLocal δ j x y a)
        map_zero' := sorry
        map_add' := sorry }

/-- The second degree-one coniveau arrow, assembled from local divisor orders. -/
noncomputable def degreeOneSecond {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ) :
    Term X δ 1 j →+ Term X δ 0 (j - 1) :=
  @DirectSum.toAddMonoid _ _ _ (Classical.decEq _) _ _
    fun x ↦
      { toFun a := ∑ᶠ y, termOf y (degreeOneSecondLocal δ j x y a)
        map_zero' := sorry
        map_add' := sorry }

/-- Evaluating the first degree-one arrow on a homogeneous summand is the corresponding local
tame-symbol sum. -/
theorem degreeOneFirst_of {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j + 1}) (a : Group 2 (X.residueField x.1)) :
    degreeOneFirst δ j (termOf x a) =
      ∑ᶠ y, termOf y (degreeOneFirstLocal δ j x y a) := sorry

/-- Evaluating the second degree-one arrow on a homogeneous summand is the corresponding local
divisor-order sum. -/
theorem degreeOneSecond_of {X : Scheme.{u}} [IsNoetherian X]
    (δ : X → ℤ) [IsDimensionFunction δ] (j : ℤ)
    (x : {x : X // δ x = j}) (a : Group 1 (X.residueField x.1)) :
    degreeOneSecond δ j (termOf x a) =
      ∑ᶠ y, termOf y (degreeOneSecondLocal δ j x y a) := sorry

end MilnorK.Coniveau
