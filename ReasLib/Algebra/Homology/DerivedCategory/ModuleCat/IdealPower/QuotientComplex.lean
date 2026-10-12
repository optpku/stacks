/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.IdealPower.Quotient
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal.Change
public import ReasLib.Algebra.Homology.HomologicalComplex.ModIdeal.Tensor
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor
public import ReasLib.Algebra.Category.CommRingCat.IdealPower
public import ReasLib.CategoryTheory.Pro.Sequential.Isomorphism
public import ReasLib.CategoryTheory.Pro.Sequential.Shift
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived ideal-power tensor and quotient-complex systems

For a cochain complex `M` over a commutative ring `A`, this leaf owns both sides of the
comparison

`M ⊗ᴸ[A] (A ⧸ I ^ (n + 1))[0] ⟶ M / I ^ (n + 1) M`.

The zero-based sequential facade represents the positive exponents: stage `n` means exponent
`n + 1`.  The comparison map is concrete.  It is the two-variable derived-tensor counit followed
by the chain map which keeps the unique degree-zero summand and applies the standard
right-tensor/quotient equivalence.  Only compatibility and the pro-isomorphism theorem are proof
obligations; no stagewise isomorphism is asserted.

-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open ComplexShape
open Opposite

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.IdealPower.QuotientComplex

variable {A : Type u} [CommRing A]

/-- The termwise quotient of `M` by `I ^ (n + 1)`, regarded as an `A`-linear cochain complex. -/
@[stacks 0G9M "positive ideal-power quotient complex"]
abbrev quotientComplex (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    CochainComplex (ModuleCat A) ℤ :=
  HomologicalComplex.ModIdeal.restrictedComplex (I ^ (n + 1)) M

/-- The derived-category object represented by the positive ideal-power quotient complex at stage `n`. -/
@[stacks 0G9M "positive ideal-power quotient-complex stage"]
abbrev stage (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    DerivedCategory (ModuleCat A) :=
  DerivedCategory.Q.obj (quotientComplex I M n)

/-- The transition from quotient exponent `n + 2` to exponent `n + 1`. -/
@[stacks 0G9M "positive ideal-power quotient-complex transition"]
noncomputable abbrev step (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    stage I M (n + 1) ⟶ stage I M n :=
  DerivedCategory.Q.map
    (HomologicalComplex.ModIdeal.restrictedOfLE
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) M)

/-- The sequential inverse system of termwise positive ideal-power quotient complexes. -/
@[stacks 0G9M "positive ideal-power quotient-complex system"]
noncomputable abbrev system (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  Functor.ofOpSequence (X := fun n ↦ stage I M n) (step I M)

/-- The underlying `A`-module of the canonical positive quotient-ring stage
`CommRingCat.IdealPower.Positive.stage I n`.  This is a comparison model for the existing
ideal-power tower, not a new tower owner. -/
@[stacks 0G9M "positive ideal-power quotient-ring module"]
abbrev ringStage (I : Ideal A) (n : ℕ) : ModuleCat A :=
  ModuleCat.of A (CommRingCat.IdealPower.Positive.stage I n : Type u)

/-- The quotient-ring stage is canonically the regular-module stage of
`Ideal.PowerQuotient.positiveSystem`. -/
@[stacks 0G9M "quotient-ring and regular-module ideal-power stages"]
noncomputable def ringStageIso (I : Ideal A) (n : ℕ) :
    ringStage I n ≅
      Ideal.PowerQuotient.positiveStage I (ModuleCat.of A A) n :=
  ((TensorProduct.lid A (A ⧸ I ^ (n + 1))).symm ≪≫ₗ
    TensorProduct.tensorQuotEquivQuotSMul A (I ^ (n + 1))).toModuleIso

/-- The `A`-linear map underlying the canonical quotient-ring transition
`CommRingCat.IdealPower.Positive.step I n`. -/
@[stacks 0G9M "positive ideal-power quotient-ring module transition"]
noncomputable abbrev ringStep (I : Ideal A) (n : ℕ) :
    ringStage I (n + 1) ⟶ ringStage I n :=
  ModuleCat.ofHom
    ((Ideal.Quotient.factorₐ A
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))).toLinearMap)

/-- The quotient-ring/module-stage comparison commutes with the canonical positive
ideal-power transitions. -/
@[stacks 0G9M "naturality of the quotient-ring stage comparison"]
theorem ringStageIso_hom_naturality (I : Ideal A) (n : ℕ) :
    ringStep I n ≫ (ringStageIso I n).hom =
      (ringStageIso I (n + 1)).hom ≫
        Ideal.PowerQuotient.positiveStep I (ModuleCat.of A A) n := sorry

/-- The degree-zero cochain model of the canonical positive quotient-ring stage. -/
@[stacks 0G9M "positive ideal-power quotient-ring complex"]
abbrev singleStage (I : Ideal A) (n : ℕ) : CochainComplex (ModuleCat A) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
    (ringStage I n)

/-- Applying the degree-zero single-complex functor to `ringStageIso` identifies the ring-stage
model with the existing regular-module quotient stage. -/
@[stacks 0G9M "degree-zero quotient-ring and regular-module stages"]
noncomputable def singleStageIso (I : Ideal A) (n : ℕ) :
    singleStage I n ≅
      (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).obj
        (Ideal.PowerQuotient.positiveStage I (ModuleCat.of A A) n) :=
  (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).mapIso
    (ringStageIso I n)

/-- The cochain map between consecutive degree-zero quotient-ring stages. -/
@[stacks 0G9M "positive ideal-power quotient-ring complex transition"]
noncomputable abbrev singleStep (I : Ideal A) (n : ℕ) :
    singleStage I (n + 1) ⟶ singleStage I n :=
  (CochainComplex.singleFunctor (ModuleCat A) (0 : ℤ)).map
    (ringStep I n)

/-- The derived tensor stage `M ⊗ᴸ[A] (A ⧸ I ^ (n + 1))[0]`. -/
@[stacks 0G9M "positive ideal-power derived tensor stage"]
noncomputable abbrev standardStage
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    DerivedCategory (ModuleCat A) :=
  (DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj M)).obj
    (DerivedCategory.Q.obj (singleStage I n))

/-- The derived-tensor transition induced by the canonical quotient-ring map. -/
@[stacks 0G9M "positive ideal-power derived tensor transition"]
noncomputable def standardStep
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    standardStage I M (n + 1) ⟶ standardStage I M n :=
  (DerivedTensor.Bifunctor.leftFunctor (DerivedCategory.Q.obj M)).map
    (DerivedCategory.Q.map (singleStep I n))

/-- The sequential inverse system `n ↦ M ⊗ᴸ[A] (A ⧸ I ^ (n + 1))[0]`. -/
@[stacks 0G9M "positive ideal-power derived tensor system"]
noncomputable def standardSystem
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    SequentialInverseSystem (DerivedCategory (ModuleCat A)) :=
  Functor.ofOpSequence (X := fun n ↦ standardStage I M n) (standardStep I M)

/-- At the surviving degree-zero summand, right tensoring by `A ⧸ I ^ (n + 1)` is the
corresponding termwise quotient of `M`. -/
@[stacks 0G9M "right tensor with an ideal quotient in one cochain degree"]
noncomputable def quotientTermIso
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) (i : ℤ) :
    ((curriedTensor (ModuleCat A)).obj (M.X i)).obj ((singleStage I n).X 0) ≅
      (quotientComplex I M n).X i :=
  ((curriedTensor (ModuleCat A)).obj (M.X i)).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ)
        (ringStage I n)) ≪≫
    HomologicalComplex.Hom.isoApp
      (HomologicalComplex.ModIdeal.tensorRightQuotientIso (I ^ (n + 1)) M) i

/-- If a tensor summand has second degree zero and total degree `i`, then its first degree is
`i`. -/
@[stacks 0G9M "degree bookkeeping for the surviving tensor summand"]
theorem firstDegree_eq
    {p q i : ℤ}
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = i)
    (hq : q = 0) : p = i := sorry

/-- The map on a tensor summand whose second degree is zero, transported to the unique surviving
first degree. -/
@[stacks 0G9M "surviving degree-zero tensor summand map"]
noncomputable def zeroSummandMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ)
    {p i : ℤ} (hpi : p = i) :
    ((curriedTensor (ModuleCat A)).obj (M.X p)).obj ((singleStage I n).X 0) ⟶
      (quotientComplex I M n).X i :=
  eqToHom
      (congrArg
        (fun k ↦ ((curriedTensor (ModuleCat A)).obj (M.X k)).obj ((singleStage I n).X 0))
        hpi) ≫
    (quotientTermIso I M n i).hom

/-- The summand map defining the tensor-to-quotient comparison: only the degree-zero quotient
ring summand survives. -/
@[stacks 0G9M "tensor-to-quotient summand map"]
noncomputable def summandMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) (i p q : ℤ)
    (h : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q) = i) :
    ((curriedTensor (ModuleCat A)).obj (M.X p)).obj ((singleStage I n).X q) ⟶
      (quotientComplex I M n).X i :=
  dite (q = 0)
    (fun hq ↦
      eqToHom
          (congrArg
            (fun k ↦ ((curriedTensor (ModuleCat A)).obj (M.X p)).obj ((singleStage I n).X k))
            hq) ≫
        zeroSummandMap I M n (firstDegree_eq h hq))
    (fun _ ↦ 0)

/-- The degree-`i` component of the ordinary tensor-complex comparison with the termwise
quotient complex. -/
@[stacks 0G9M "ordinary tensor-to-quotient component"]
noncomputable def quotientTensorComponent
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) (i : ℤ) :
    (HomologicalComplex.tensorObj M (singleStage I n)).X i ⟶
      (quotientComplex I M n).X i :=
  HomologicalComplex.mapBifunctorDesc
    (K₁ := M) (K₂ := singleStage I n)
    (F := curriedTensor (ModuleCat A)) (c := ComplexShape.up ℤ)
    (A := (quotientComplex I M n).X i) (j := i)
    (summandMap I M n i)

/-- The degreewise tensor-to-quotient components commute with the cochain differential. -/
@[stacks 0G9M "tensor-to-quotient differential compatibility"]
theorem quotientTensorComponent_comm
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    quotientTensorComponent I M n i ≫ (quotientComplex I M n).d i j =
      (HomologicalComplex.tensorObj M (singleStage I n)).d i j ≫
        quotientTensorComponent I M n j := sorry

/-- The concrete chain map from ordinary tensor totalization to termwise reduction. -/
@[stacks 0G9M "ordinary tensor-to-quotient comparison"]
noncomputable def quotientTensorMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    HomologicalComplex.tensorObj M (singleStage I n) ⟶ quotientComplex I M n where
  f i := quotientTensorComponent I M n i
  comm' i j hij := quotientTensorComponent_comm I M n i j hij

/-- The degree-`i` map of `quotientTensorMap` is the descended summand comparison. -/
@[simp, stacks 0G9M "component formula for the tensor-to-quotient map"]
theorem quotientTensorMap_f
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) (i : ℤ) :
    (quotientTensorMap I M n).f i = quotientTensorComponent I M n i := sorry

/-- The stage comparison from derived tensor to the termwise quotient complex. -/
@[stacks 0G9M "derived tensor-to-quotient stage comparison"]
noncomputable def comparisonApp
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    standardStage I M n ⟶ stage I M n :=
  DerivedTensor.Bifunctor.counitAppOfQ M (singleStage I n) ≫
    DerivedCategory.Q.map (quotientTensorMap I M n)

/-- Consecutive derived tensor-to-quotient comparisons commute with the explicit ideal-power
transitions. -/
@[stacks 0G9M "explicit transition compatibility of the derived tensor comparison"]
theorem comparisonApp_step
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    standardStep I M n ≫ comparisonApp I M n =
      comparisonApp I M (n + 1) ≫ step I M n := sorry

/-- The stage comparisons commute with the successor maps of the two inverse systems. -/
@[stacks 0G9M "naturality of the derived tensor-to-quotient comparison"]
theorem comparisonApp_naturality
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (standardSystem I M).stepMap n ≫ comparisonApp I M n =
      comparisonApp I M (n + 1) ≫ (system I M).stepMap n := sorry

/-- The stage comparisons assemble into a natural transformation of sequential inverse
systems. -/
@[stacks 0G9M "derived tensor-to-quotient natural transformation"]
noncomputable def comparisonNatTrans
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    standardSystem I M ⟶ system I M :=
  NatTrans.ofOpSequence (comparisonApp I M) (comparisonApp_naturality I M)

/-- The sequential pro-morphism represented by the canonical stage comparisons. -/
@[stacks 0G9M "derived tensor-to-quotient sequential pro-morphism"]
noncomputable def comparison
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    Pro.SequentialHom (standardSystem I M) (system I M) :=
  Pro.SequentialHom.ofNatTrans (comparisonNatTrans I M)

/-- For a bounded complex of finite modules over a Noetherian ring, the canonical derived
tensor-to-quotient comparison is an isomorphism of pro-objects. -/
@[stacks 0G9M "derived tensor comparison with ideal-power quotient complexes"]
theorem comparison_isIso [IsNoetherianRing A]
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    IsIso (comparison I M).toHom := sorry

/-- The object formula for the quotient-complex inverse system. -/
@[simp, stacks 0G9M "object formula for the quotient-complex system"]
theorem system_obj (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (system I M).obj (op n) = stage I M n := sorry

/-- The successor map of the quotient-complex inverse system is `step`. -/
@[simp, stacks 0G9M "transition formula for the quotient-complex system"]
theorem system_stepMap (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (system I M).stepMap n = step I M n := sorry

/-- The object formula for the derived tensor inverse system. -/
@[simp, stacks 0G9M "object formula for the derived tensor system"]
theorem standardSystem_obj
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (standardSystem I M).obj (op n) = standardStage I M n := sorry

/-- The successor map of the derived tensor inverse system is `standardStep`. -/
@[simp, stacks 0G9M "transition formula for the derived tensor system"]
theorem standardSystem_stepMap
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (standardSystem I M).stepMap n = standardStep I M n := sorry

/-- The component formula for the natural transformation underlying `comparison`. -/
@[simp, stacks 0G9M "component formula for the derived tensor comparison"]
theorem comparisonNatTrans_app
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (comparisonNatTrans I M).app (op n) = comparisonApp I M n := sorry

/-- The canonical comparison representative uses the identity reindexing. -/
@[simp, stacks 0G9M "identity reindexing of the derived tensor comparison"]
theorem comparison_reindex
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) :
    (comparison I M).reindex = OrderHom.id := sorry

/-- The level map of the canonical comparison representative is `comparisonApp`. -/
@[simp, stacks 0G9M "level map of the derived tensor comparison"]
theorem comparison_hom_app
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ) (n : ℕ) :
    (comparison I M).hom.app (op n) = comparisonApp I M n := sorry

/-- For a bounded complex of finite modules over a Noetherian ring, the derived
tensor-to-quotient comparison admits a uniform shifted inverse. -/
@[stacks 0GA5]
theorem comparison_hasShiftInverse [IsNoetherianRing A]
    (I : Ideal A) (M : CochainComplex (ModuleCat A) ℤ)
    (hboundedBelow : ∃ a : ℤ, M.IsStrictlyGE a)
    (hboundedAbove : ∃ b : ℤ, M.IsStrictlyLE b)
    (hfinite : ∀ i : ℤ, Module.Finite A (M.X i)) :
    ∃ c : ℕ, ∃ β : (system I M).shift c ⟶ standardSystem I M,
      Pro.SequentialHom.IsShiftInverse (comparisonNatTrans I M) c β := sorry

end CategoryTheory.DerivedCategory.IdealPower.QuotientComplex
