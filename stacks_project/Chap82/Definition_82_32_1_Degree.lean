module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap82.Lemma_82_16_3

/-!
# Degree of zero-cycle classes on proper algebraic spaces over a field

The degree homomorphism on `CH_0(X)` is proper pushforward to `Spec k`,
followed by the natural identification `CH_0(Spec k) ≃+ ℤ` sending
`[Spec k]` to `1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- `Spec k` as an algebraic space over itself. -/
abbrev specFieldSpace (k : Type u) [Field k] :
    AlgebraicSpace (Spec (CommRingCat.of k)) :=
  ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))

/-- `specFieldSpace k` is `Spec k` viewed as an algebraic space over itself. -/
theorem specFieldSpace_eq (k : Type u) [Field k] :
    specFieldSpace k = ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  sorry

/-- `Spec k`, viewed as an algebraic space over itself, is universally catenary. -/
instance instUniversallyCatenary_specFieldSpace (k : Type u) [Field k] :
    UniversallyCatenary (specFieldSpace k) :=
  sorry

/-- `Spec k`, viewed as an algebraic space over itself, is quasi-separated. -/
instance instIsQuasiSeparated_specFieldSpace (k : Type u) [Field k] :
    IsQuasiSeparated (specFieldSpace k) :=
  sorry

/-- The points of `Spec k` as an algebraic space form a `T₁` space. -/
instance instT1Space_points_specFieldSpace (k : Type u) [Field k] :
    T1Space (Points (specFieldSpace k)) :=
  sorry

/-- The structure morphism of `Spec k` as an algebraic space over itself is proper. -/
instance instProper_toBase_specFieldSpace (k : Type u) [Field k] :
    Proper (toBase (specFieldSpace k)) :=
  sorry

namespace Hom

/-- The Chow group `CH_k(X)` of `k`-cycles modulo rational equivalence. -/
noncomputable abbrev chowGroup {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ) :=
  cycleGroup f δ k ⧸ RationalEquivalence.boundaries f δ k

/-- The Chow group is the quotient of `Z_k(X)` by rational equivalence. -/
theorem chowGroup_eq {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    chowGroup f δ k =
      (cycleGroup f δ k ⧸ RationalEquivalence.boundaries f δ k) :=
  sorry

/-- The canonical quotient map `Z_k(X) → CH_k(X)`. -/
noncomputable abbrev chowMk {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    cycleGroup f δ k →+ chowGroup f δ k :=
  QuotientAddGroup.mk' (RationalEquivalence.boundaries f δ k)

/-- A cycle has zero Chow class exactly when it is rationally equivalent to
zero. -/
theorem chowMk_eq_zero_iff {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (k : ℤ)
    (α : cycleGroup f δ k) :
    chowMk f δ k α = 0 ↔ RationalEquivalence.IsRationallyTrivial f δ k α :=
  sorry

/-- The unique scheme-theoretic point of `Spec k`. -/
def specFieldSchemePoint (k : Type u) [Field k] :
    (Over.mk (𝟙 (Spec (CommRingCat.of k)))).left :=
  (default : Spec (CommRingCat.of k))

/-- `specFieldSchemePoint k` is the unique point of `Spec k`. -/
theorem specFieldSchemePoint_eq (k : Type u) [Field k] :
    specFieldSchemePoint k = (default : Spec (CommRingCat.of k)) :=
  sorry

/-- The unique point of `Spec k` as an algebraic space over itself. -/
def specFieldPoint (k : Type u) [Field k] : Points (specFieldSpace k) :=
  ofOver.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (specFieldSchemePoint k)

/-- `specFieldPoint k` is the image of the unique scheme point of `Spec k`. -/
theorem specFieldPoint_eq (k : Type u) [Field k] :
    specFieldPoint k =
      ofOver.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (specFieldSchemePoint k) :=
  sorry

/-- Points of `Spec k` as an algebraic space are unique. -/
instance instUnique_points_specFieldSpace (k : Type u) [Field k] :
    Unique (Points (specFieldSpace k)) where
  default := specFieldPoint k
  uniq := sorry

/-- The generator `[Spec k]` is the singleton `1`-cycle at the unique point of
`Spec k`. -/
theorem specFieldFundamentalCycle_mem (k : Type u) [Field k] :
    @locallyFinsuppWithin.single (Points (specFieldSpace k)) _ ℤ
        (Classical.decEq _) _ (specFieldPoint k) 1 ∈
      cycleGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0 :=
  sorry

/-- The fundamental `0`-cycle `[Spec k]` on `Spec k`. -/
def specFieldFundamentalCycle (k : Type u) [Field k] :
    cycleGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0 :=
  ⟨@locallyFinsuppWithin.single (Points (specFieldSpace k)) _ ℤ
      (Classical.decEq _) _ (specFieldPoint k) 1,
    specFieldFundamentalCycle_mem k⟩

/-- The fundamental cycle is the singleton supported at the unique point of
`Spec k`. -/
theorem specFieldFundamentalCycle_apply (k : Type u) [Field k]
    (x : Points (specFieldSpace k)) :
    (specFieldFundamentalCycle k :
        Function.locallyFinsupp (Points (specFieldSpace k)) ℤ) x =
      if x = specFieldPoint k then (1 : ℤ) else 0 :=
  sorry

/-- The fundamental class `[Spec k]` in `CH_0(Spec k)`. -/
def specFieldFundamentalClass (k : Type u) [Field k] :
    chowGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0 :=
  chowMk (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0
    (specFieldFundamentalCycle k)

/-- The fundamental class is the Chow class of the fundamental cycle. -/
theorem specFieldFundamentalClass_eq (k : Type u) [Field k] :
    specFieldFundamentalClass k =
      chowMk (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0
        (specFieldFundamentalCycle k) :=
  sorry

/-- Evaluation of a `0`-cycle on `Spec k` at the unique point. -/
def specFieldCycleEval (k : Type u) [Field k] :
    cycleGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0 →+ ℤ where
  toFun α :=
    (α : Function.locallyFinsupp (Points (specFieldSpace k)) ℤ) (specFieldPoint k)
  map_zero' := sorry
  map_add' := sorry

/-- Cycle-level evaluation on `Spec k` is the coefficient of the unique point. -/
theorem specFieldCycleEval_apply (k : Type u) [Field k]
    (α : cycleGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0) :
    specFieldCycleEval k α =
      (α : Function.locallyFinsupp (Points (specFieldSpace k)) ℤ)
        (specFieldPoint k) :=
  sorry

/-- Rational-equivalence boundaries on `Spec k` have cycle-level degree zero. -/
theorem specFieldBoundaries_le_ker_cycleEval (k : Type u) [Field k] :
    RationalEquivalence.boundaries (toBase (specFieldSpace k))
        (fun _ ↦ (0 : ℤ)) 0 ≤
      (specFieldCycleEval k).ker :=
  sorry

/-- Evaluation `CH_0(Spec k) →+ ℤ` induced by the coefficient of `[Spec k]`. -/
def specFieldChowEval (k : Type u) [Field k] :
    chowGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0 →+ ℤ :=
  QuotientAddGroup.lift
    (RationalEquivalence.boundaries (toBase (specFieldSpace k))
      (fun _ ↦ (0 : ℤ)) 0)
    (specFieldCycleEval k) (specFieldBoundaries_le_ker_cycleEval k)

/-- Evaluation of a Chow class on `Spec k` recovers the cycle-level coefficient. -/
theorem specFieldChowEval_chowMk (k : Type u) [Field k]
    (α : cycleGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0) :
    specFieldChowEval k
        (chowMk (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0 α) =
      specFieldCycleEval k α :=
  sorry

/-- The inverse `ℤ →+ CH_0(Spec k)` sending `n` to `n • [Spec k]`. -/
def specFieldChowOfInt (k : Type u) [Field k] :
    ℤ →+ chowGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0 where
  toFun n := n • specFieldFundamentalClass k
  map_zero' := sorry
  map_add' := sorry

/-- The inverse homomorphism is scalar multiplication of the fundamental
class. -/
theorem specFieldChowOfInt_apply (k : Type u) [Field k] (n : ℤ) :
    specFieldChowOfInt k n = n • specFieldFundamentalClass k :=
  sorry

/-- The natural isomorphism `CH_0(Spec k) ≃+ ℤ` sending `[Spec k]` to `1`. -/
def specFieldChowEquiv (k : Type u) [Field k] :
    chowGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0 ≃+ ℤ where
  toFun := specFieldChowEval k
  invFun := specFieldChowOfInt k
  left_inv := sorry
  right_inv := sorry
  map_add' := sorry

/-- The additive equivalence evaluates as `specFieldChowEval`. -/
theorem specFieldChowEquiv_apply (k : Type u) [Field k]
    (α : chowGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0) :
    specFieldChowEquiv k α = specFieldChowEval k α :=
  sorry

/-- The natural isomorphism sends `[Spec k]` to `1`. -/
theorem specFieldChowEquiv_fundamentalClass (k : Type u) [Field k] :
    specFieldChowEquiv k (specFieldFundamentalClass k) = 1 :=
  sorry

/-- Proper pushforward of zero-cycle classes along the structure morphism
`X ⟶ Spec k`. -/
def chowPushforwardToSpec {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)] :
    chowGroup (toBase X) (fun _ ↦ (0 : ℤ)) 0 →+
      chowGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0 :=
  QuotientAddGroup.map
    (RationalEquivalence.boundaries (toBase X) (fun _ ↦ (0 : ℤ)) 0)
    (RationalEquivalence.boundaries (toBase (specFieldSpace k))
      (fun _ ↦ (0 : ℤ)) 0)
    (properPushforwardHom (toBase X) (toBase (specFieldSpace k))
      (fun _ ↦ (0 : ℤ)) (toBase X)
      (eq_toBase (toBase X ≫ toBase (specFieldSpace k))) 0)
    (properPushforwardHom_mem_boundaries (toBase X)
      (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) (toBase X)
      (eq_toBase (toBase X ≫ toBase (specFieldSpace k))) 0)

/-- Chow-level pushforward to `Spec k` is induced by cycle-level proper
pushforward. -/
theorem chowPushforwardToSpec_chowMk {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)]
    (α : cycleGroup (toBase X) (fun _ ↦ (0 : ℤ)) 0) :
    chowPushforwardToSpec (chowMk (toBase X) (fun _ ↦ (0 : ℤ)) 0 α) =
      chowMk (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0
        (properPushforwardHom (toBase X) (toBase (specFieldSpace k))
          (fun _ ↦ (0 : ℤ)) (toBase X)
          (eq_toBase (toBase X ≫ toBase (specFieldSpace k))) 0 α) :=
  sorry

/-- The degree of a zero-cycle class on a proper algebraic space over a field. -/
def chowDegree {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)] :
    chowGroup (toBase X) (fun _ ↦ (0 : ℤ)) 0 →+ ℤ :=
  (specFieldChowEval k).comp chowPushforwardToSpec

/-- Degree is proper pushforward to `Spec k` composed with evaluation
`CH_0(Spec k) →+ ℤ`. -/
theorem chowDegree_eq_comp {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)] :
    (chowDegree : chowGroup (toBase X) (fun _ ↦ (0 : ℤ)) 0 →+ ℤ) =
      (specFieldChowEval k).comp
        (chowPushforwardToSpec :
          chowGroup (toBase X) (fun _ ↦ (0 : ℤ)) 0 →+
            chowGroup (toBase (specFieldSpace k)) (fun _ ↦ (0 : ℤ)) 0) :=
  sorry

/-- Degree of a Chow class is evaluation of the isomorphism on the pushed-forward
class. -/
theorem chowDegree_apply {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)]
    (α : chowGroup (toBase X) (fun _ ↦ (0 : ℤ)) 0) :
    chowDegree α = specFieldChowEquiv k (chowPushforwardToSpec α) :=
  sorry

/-- On cycle classes, Chow-level degree is the coefficient of the unique point
of `Spec k` after proper pushforward. -/
theorem chowDegree_chowMk {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)]
    (α : cycleGroup (toBase X) (fun _ ↦ (0 : ℤ)) 0) :
    chowDegree (chowMk (toBase X) (fun _ ↦ (0 : ℤ)) 0 α) =
      properPushforwardCycle (toBase X) (toBase (specFieldSpace k))
        (fun _ ↦ (0 : ℤ)) (toBase X)
        (eq_toBase (toBase X ≫ toBase (specFieldSpace k)))
        (α : Function.locallyFinsupp (Points X) ℤ) (specFieldPoint k) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
