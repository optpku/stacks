/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IntersectionTheory.FirstChernChow
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.AssociatedCycle

/-! # Iterated first Chern intersection and closed-subspace Chow classes -/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.AlgebraicSpace.IntersectionTheory

noncomputable section

universe u

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
            ((AddEquiv.cast (M := Hom.chowGroup f δ) (Nat.cast_succ n)).toAddMonoidHom))
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
          ((AddEquiv.cast (M := Hom.chowGroup f δ) (Nat.cast_succ d)).toAddMonoidHom)) :=
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
        ((AddEquiv.cast (M := Hom.chowGroup f δ) (Nat.cast_succ d).symm).toAddMonoidHom
          (chowMk f δ ((d : ℤ) + 1) α)) =
      iteratedFirstChernClassCap f δ d (fun j ↦ L j.castSucc)
        (firstChernClassCap f δ (L (Fin.last d)) d α) :=
  sorry

/-- The associated degree-`k` cycle of a closed subspace is supported in degree `k`. -/
private theorem closedSubspaceClass_cycle_mem
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ) :
    @ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Y
        (relativeDimensionFunction f δ) k ∈ cycleGroup f δ k := sorry

/-- The Chow class `[Y]_k` of a closed subspace. -/
noncomputable def closedSubspaceClass
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ) : chowGroup f δ k :=
  chowMk f δ k
    ⟨@ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Y
        (relativeDimensionFunction f δ) k,
      by exact closedSubspaceClass_cycle_mem f δ Y k⟩

/-- The closed-subspace Chow class is the image of the associated cycle. -/
theorem closedSubspaceClass_eq
    {S : Scheme.{u}} {B X : AlgebraicSpace S}
    [UniversallyCatenary B] [IsQuasiSeparated B]
    (f : X ⟶ B) [QuasiSeparated f] [LocallyOfFiniteType f]
    (δ : Points B → ℤ) [IsDimensionFunction δ]
    (Y : ClosedSubspace X) (k : ℤ) :
    closedSubspaceClass f δ Y k =
      chowMk f δ k
        ⟨@ClosedSubspace.associatedCycle S X (LocallyOfFiniteType.isLocallyNoetherian f) Y
            (relativeDimensionFunction f δ) k,
          by exact closedSubspaceClass_cycle_mem f δ Y k⟩ := rfl

end AlgebraicGeometry.AlgebraicSpace.Hom

