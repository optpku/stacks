/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Equiv.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SpecField
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SchemeRealization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.ProperPushforward

/-! # Degree of zero-cycle classes on proper algebraic spaces over fields -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The structure morphism of `Spec k` as an algebraic space over itself is proper. -/
instance instProper_toBase_ofOver_specField (k : Type u) [Field k] :
    Proper (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- The generator `[Spec k]` is the singleton `1`-cycle at the unique point of
`Spec k`. -/
theorem specFieldFundamentalCycle_mem (k : Type u) [Field k] :
    @Function.locallyFinsuppWithin.single (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) _ ℤ
        (Classical.decEq _) _ (Points.specFieldPoint k) 1 ∈
      cycleGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 :=
  sorry

/-- The fundamental `0`-cycle `[Spec k]` on `Spec k`. -/
def specFieldFundamentalCycle (k : Type u) [Field k] :
    cycleGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 :=
  ⟨@Function.locallyFinsuppWithin.single (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) _ ℤ
      (Classical.decEq _) _ (Points.specFieldPoint k) 1,
    specFieldFundamentalCycle_mem k⟩

/-- The fundamental cycle is the singleton supported at the unique point of
`Spec k`. -/
theorem specFieldFundamentalCycle_apply (k : Type u) [Field k]
    (x : Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :
    (specFieldFundamentalCycle k :
        Function.locallyFinsupp (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) ℤ) x =
      if x = Points.specFieldPoint k then (1 : ℤ) else 0 :=
  sorry

/-- The fundamental class `[Spec k]` in `CH_0(Spec k)`. -/
def specFieldFundamentalClass (k : Type u) [Field k] :
    chowGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 :=
  chowMk (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0
    (specFieldFundamentalCycle k)

/-- The fundamental class is the Chow class of the fundamental cycle. -/
theorem specFieldFundamentalClass_eq (k : Type u) [Field k] :
    specFieldFundamentalClass k =
      chowMk (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0
        (specFieldFundamentalCycle k) := rfl

/-- Evaluation of a `0`-cycle on `Spec k` at the unique point. -/
def specFieldCycleEval (k : Type u) [Field k] :
    cycleGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 →+ ℤ where
  toFun α :=
    (α : Function.locallyFinsupp
        (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) ℤ)
      (Points.specFieldPoint k)
  map_zero' := rfl
  map_add' := fun _ _ ↦ rfl

/-- Cycle-level evaluation on `Spec k` is the coefficient of the unique point. -/
theorem specFieldCycleEval_apply (k : Type u) [Field k]
    (α : cycleGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0) :
    specFieldCycleEval k α =
      (α : Function.locallyFinsupp
          (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) ℤ)
        (Points.specFieldPoint k) := rfl

/-- Rational-equivalence boundaries on `Spec k` have cycle-level degree zero. -/
theorem specFieldBoundaries_le_ker_cycleEval (k : Type u) [Field k] :
    RationalEquivalence.boundaries
        (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
        (fun _ ↦ (0 : ℤ)) 0 ≤
      (specFieldCycleEval k).ker :=
  sorry

/-- Evaluation `CH_0(Spec k) →+ ℤ` induced by the coefficient of `[Spec k]`. -/
def specFieldChowEval (k : Type u) [Field k] :
    chowGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 →+ ℤ :=
  QuotientAddGroup.lift
    (RationalEquivalence.boundaries
      (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0)
    (specFieldCycleEval k) (specFieldBoundaries_le_ker_cycleEval k)

/-- Evaluation of a Chow class on `Spec k` recovers the cycle-level coefficient. -/
theorem specFieldChowEval_chowMk (k : Type u) [Field k]
    (α : cycleGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0) :
    specFieldChowEval k
        (chowMk (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
          (fun _ ↦ (0 : ℤ)) 0 α) =
      specFieldCycleEval k α :=
  sorry

/-- The inverse `ℤ →+ CH_0(Spec k)` sending `n` to `n • [Spec k]`. -/
def specFieldChowOfInt (k : Type u) [Field k] :
    ℤ →+ chowGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 where
  toFun n := n • specFieldFundamentalClass k
  map_zero' := sorry
  map_add' := sorry

/-- The inverse homomorphism is scalar multiplication of the fundamental
class. -/
theorem specFieldChowOfInt_apply (k : Type u) [Field k] (n : ℤ) :
    specFieldChowOfInt k n = n • specFieldFundamentalClass k := rfl

/-- The natural isomorphism `CH_0(Spec k) ≃+ ℤ` sending `[Spec k]` to `1`. -/
def specFieldChowEquiv (k : Type u) [Field k] :
    chowGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 ≃+ ℤ where
  toFun := specFieldChowEval k
  invFun := specFieldChowOfInt k
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The additive equivalence evaluates as `specFieldChowEval`. -/
theorem specFieldChowEquiv_apply (k : Type u) [Field k]
    (α : chowGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0) :
    specFieldChowEquiv k α = specFieldChowEval k α := rfl

/-- The natural isomorphism sends `[Spec k]` to `1`. -/
theorem specFieldChowEquiv_fundamentalClass (k : Type u) [Field k] :
    specFieldChowEquiv k (specFieldFundamentalClass k) = 1 :=
  sorry

/-- Proper pushforward of zero-cycle classes along the structure morphism
`X ⟶ Spec k`. -/
def chowPushforwardToSpec {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)] :
    chowGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0 →+
      chowGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
        (fun _ ↦ (0 : ℤ)) 0 :=
  ChowGroup.properPushforward (SchemeRealization.toBase X)
    (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    (fun _ ↦ (0 : ℤ)) (SchemeRealization.toBase X)
    (SchemeRealization.eq_toBase (SchemeRealization.toBase X ≫
      SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))) 0

/-- Chow-level pushforward to `Spec k` is induced by cycle-level proper
pushforward. -/
theorem chowPushforwardToSpec_chowMk {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)]
    (α : cycleGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0) :
    chowPushforwardToSpec (chowMk (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0 α) =
      chowMk (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0
        (properPushforwardHom (SchemeRealization.toBase X)
          (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
          (fun _ ↦ (0 : ℤ)) (SchemeRealization.toBase X)
          (SchemeRealization.eq_toBase (SchemeRealization.toBase X ≫
            SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))) 0 α) :=
  sorry

/-- The degree of a zero-cycle class on a proper algebraic space over a field. -/
def chowDegree {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)] :
    chowGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0 →+ ℤ :=
  (specFieldChowEval k).comp chowPushforwardToSpec

/-- Degree is proper pushforward to `Spec k` composed with evaluation
`CH_0(Spec k) →+ ℤ`. -/
theorem chowDegree_eq_comp {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)] :
    (chowDegree : chowGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0 →+ ℤ) =
      (specFieldChowEval k).comp
        (chowPushforwardToSpec :
          chowGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0 →+
            chowGroup (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
              (fun _ ↦ (0 : ℤ)) 0) := rfl

/-- Degree of a Chow class is evaluation of the isomorphism on the pushed-forward
class. -/
theorem chowDegree_apply {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)]
    (α : chowGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0) :
    chowDegree α = specFieldChowEquiv k (chowPushforwardToSpec α) :=
  sorry

/-- On cycle classes, Chow-level degree is the coefficient of the unique point
of `Spec k` after proper pushforward. -/
theorem chowDegree_chowMk {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (SchemeRealization.toBase X)]
    (α : cycleGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0) :
    chowDegree (chowMk (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0 α) =
      properPushforwardCycle (SchemeRealization.toBase X)
        (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
        (fun _ ↦ (0 : ℤ)) (SchemeRealization.toBase X)
        (SchemeRealization.eq_toBase (SchemeRealization.toBase X ≫
            SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))))
        (α : Function.locallyFinsupp (Points X) ℤ) (Points.specFieldPoint k) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
