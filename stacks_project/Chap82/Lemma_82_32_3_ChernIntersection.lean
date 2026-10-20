/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap82.Lemma_82_18_4

/-!
# Iterated first-Chern caps on algebraic spaces

Successive first-Chern intersection of a finite family of invertible modules,
together with the Chow class of a closed subspace and the degree of a
zero-cycle class over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.Hom
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- `Spec k`, viewed as an algebraic space over itself, is universally catenary. -/
instance instUniversallyCatenary_ofOver_specField (k : Type u) [Field k] :
    UniversallyCatenary (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :=
  sorry

/-- `Spec k`, viewed as an algebraic space over itself, is quasi-separated. -/
instance instIsQuasiSeparated_ofOver_specField (k : Type u) [Field k] :
    IsQuasiSeparated (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :=
  sorry

/-- The spectrum of a field has a unique point. -/
instance instUnique_specOfField (k : Type u) [Field k] :
    Unique (Spec (CommRingCat.of k)) :=
  inferInstanceAs (Unique (PrimeSpectrum k))

/-- The points of `Spec k` as an algebraic space form a `T₁` space. -/
instance instT1Space_points_ofOver_specField (k : Type u) [Field k] :
    T1Space (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
  sorry

/-- The structure morphism of `Spec k` as an algebraic space over itself is proper. -/
instance instProper_toBase_ofOver_specField (k : Type u) [Field k] :
    Proper (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.AlgebraicSpace.Hom

/-- Successively cap a degree-`d` Chow class with the first Chern classes of a
`Fin d`-family of invertible modules, applying the last factor first. -/
noncomputable def iteratedFirstChernClassCap
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (d : ℕ)
    (L : Fin d → X.Modules)
    [hL : ∀ j : Fin d, isInvertibleObject (L j)] :
    chowGroup f δ d →+ chowGroup f δ 0 :=
  let rec go (n : ℕ) (M : Fin n → X.Modules)
      (hM : ∀ j : Fin n, isInvertibleObject (M j)) :
      chowGroup f δ n →+ chowGroup f δ 0 :=
    match n, M, hM with
    | 0, _, _ => AddMonoidHom.id _
    | n + 1, M, hM =>
        (go n (fun j ↦ M j.castSucc) (fun j ↦ hM j.castSucc)).comp
          ((@FirstChernChow.cap S B X _ _ f _ _ δ _ (M (Fin.last n))
              (hM (Fin.last n)) (n : ℤ)).comp
            (ChowCohomology.castChowGroup δ f (Nat.cast_succ n)))
  go d L hL

/-- The empty family acts identically on degree-zero Chow classes. -/
theorem iteratedFirstChernClassCap_zero
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (L : Fin 0 → X.Modules) [∀ j : Fin 0, isInvertibleObject (L j)] :
    iteratedFirstChernClassCap f δ 0 L = AddMonoidHom.id _ :=
  sorry

/-- Iteration over a successor family first caps with its last factor and then
iterates over the initial family. -/
theorem iteratedFirstChernClassCap_succ
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (d : ℕ)
    (L : Fin (d + 1) → X.Modules)
    [∀ j : Fin (d + 1), isInvertibleObject (L j)] :
    iteratedFirstChernClassCap f δ (d + 1) L =
      (iteratedFirstChernClassCap f δ d (fun j ↦ L j.castSucc)).comp
        ((FirstChernChow.cap f δ (L (Fin.last d)) (d : ℤ)).comp
          (ChowCohomology.castChowGroup δ f (Nat.cast_succ d))) :=
  sorry

/-- Iterated first-Chern cap of a cycle class is the cycle-level first-Chern cap
followed by iteration on the remaining factors. -/
theorem iteratedFirstChernClassCap_chowMk
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ] (d : ℕ)
    (L : Fin (d + 1) → X.Modules)
    [∀ j : Fin (d + 1), isInvertibleObject (L j)]
    (α : cycleGroup f δ ((d : ℤ) + 1)) :
    iteratedFirstChernClassCap f δ (d + 1) L
        (ChowCohomology.castChowGroup δ f (Nat.cast_succ d).symm
          (chowMk f δ ((d : ℤ) + 1) α)) =
      iteratedFirstChernClassCap f δ d (fun j ↦ L j.castSucc)
        (firstChernClassCap f δ (L (Fin.last d)) d α) :=
  sorry

/-- The Chow class `[Y]_k` of a closed subspace. -/
noncomputable def closedSubspaceClass
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ) : chowGroup f δ k :=
  chowMk f δ k
    ⟨@ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Y
        (relativeDimensionFunction f δ) k,
      closedSubspace_cycle_mem_cycleGroup f δ Y k⟩

/-- The closed-subspace Chow class is the image of the associated cycle. -/
theorem closedSubspaceClass_eq
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ) :
    closedSubspaceClass f δ Y k =
      chowMk f δ k
        ⟨@ClosedSubspace.cycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Y
            (relativeDimensionFunction f δ) k,
          closedSubspace_cycle_mem_cycleGroup f δ Y k⟩ :=
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
def specFieldPoint (k : Type u) [Field k] :
    Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :=
  ofOver.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (specFieldSchemePoint k)

/-- `specFieldPoint k` is the image of the unique scheme point of `Spec k`. -/
theorem specFieldPoint_eq (k : Type u) [Field k] :
    specFieldPoint k =
      ofOver.pointsEquiv (Over.mk (𝟙 (Spec (CommRingCat.of k))))
        (specFieldSchemePoint k) :=
  sorry

/-- Evaluation of a `0`-cycle on `Spec k` at the unique point. -/
def specFieldCycleEval (k : Type u) [Field k] :
    cycleGroup (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 →+ ℤ where
  toFun α :=
    (α : Function.locallyFinsupp
        (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) ℤ)
      (specFieldPoint k)
  map_zero' := sorry
  map_add' := sorry

/-- Cycle-level evaluation on `Spec k` is the coefficient of the unique point. -/
theorem specFieldCycleEval_apply (k : Type u) [Field k]
    (α : cycleGroup (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0) :
    specFieldCycleEval k α =
      (α : Function.locallyFinsupp
          (Points (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))))) ℤ)
        (specFieldPoint k) :=
  sorry

/-- Rational-equivalence boundaries on `Spec k` have cycle-level degree zero. -/
theorem specFieldBoundaries_le_ker_cycleEval (k : Type u) [Field k] :
    RationalEquivalence.boundaries
        (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
        (fun _ ↦ (0 : ℤ)) 0 ≤
      (specFieldCycleEval k).ker :=
  sorry

/-- Evaluation `CH_0(Spec k) →+ ℤ` induced by the coefficient of `[Spec k]`. -/
def specFieldChowEval (k : Type u) [Field k] :
    chowGroup (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 →+ ℤ :=
  QuotientAddGroup.lift
    (RationalEquivalence.boundaries
      (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0)
    (specFieldCycleEval k) (specFieldBoundaries_le_ker_cycleEval k)

/-- Evaluation of a Chow class on `Spec k` recovers the cycle-level coefficient. -/
theorem specFieldChowEval_chowMk (k : Type u) [Field k]
    (α : cycleGroup (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0) :
    specFieldChowEval k
        (chowMk (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
          (fun _ ↦ (0 : ℤ)) 0 α) =
      specFieldCycleEval k α :=
  sorry

/-- Proper pushforward of zero-cycle classes along the structure morphism
`X ⟶ Spec k`. -/
def chowPushforwardToSpec {k : Type u} [Field k]
    {X : AlgebraicSpace (Spec (CommRingCat.of k))} [Proper (toBase X)] :
    chowGroup (toBase X) (fun _ ↦ (0 : ℤ)) 0 →+
      chowGroup (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
        (fun _ ↦ (0 : ℤ)) 0 :=
  properPushforward (fun _ ↦ (0 : ℤ)) (toBase X)
    (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
    (toBase X)
    (eq_toBase (toBase X ≫
      toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))) 0

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
            chowGroup (toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
              (fun _ ↦ (0 : ℤ)) 0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Hom
