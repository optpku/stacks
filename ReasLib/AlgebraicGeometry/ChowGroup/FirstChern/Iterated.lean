module

public import ReasLib.AlgebraicGeometry.ChowGroup.FirstChern.Relative
public import ReasLib.AlgebraicGeometry.ChowGroup.Reindex

/-!
# Iterated first-Chern cap products

This module defines the successive first-Chern cap product associated to a
finite family of invertible modules and records its basic computation laws.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup

/-- Successively cap a degree-`d` Chow class with the first Chern classes of a
`Fin d`-family of invertible modules. -/
noncomputable def iteratedFirstChernClassCap
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] (d : ℕ)
    (L : Fin d → X.left.Modules)
    [hL : ∀ j : Fin d, Scheme.Modules.Invertible (L j)] :
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction delta) inferInstance (d : ℤ) →+
      @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction delta) inferInstance 0 :=
  let rec go :
      (n : ℕ) → (M : Fin n → X.left.Modules) →
        (∀ j : Fin n, Scheme.Modules.Invertible (M j)) →
        @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction delta) inferInstance (n : ℤ) →+
          @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction delta) inferInstance 0
    | 0, _, _ => AddMonoidHom.id _
    | n + 1, M, hM =>
        (go n (fun j ↦ M j.castSucc) (fun j ↦ hM j.castSucc)).comp
          ((AddEquiv.cast
            ((congrArg (fun m : ℤ ↦ m - 1) (Nat.cast_succ n)).trans
              (add_sub_cancel_right (n : ℤ) 1)) :
            @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                (X.hom.relativeDimensionFunction delta) inferInstance
                (((n + 1 : ℕ) : ℤ) - 1) ≃+
              @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                (X.hom.relativeDimensionFunction delta) inferInstance (n : ℤ)).toAddMonoidHom.comp
            (@firstChernClassCap S _ delta _ X _ (M (Fin.last n)) (hM (Fin.last n))
              ((n + 1 : ℕ) : ℤ)))
  go d L hL

/-- The empty family acts identically on degree-zero Chow classes. -/
theorem iteratedFirstChernClassCap_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom]
    (L : Fin 0 → X.left.Modules) [∀ j : Fin 0, Scheme.Modules.Invertible (L j)] :
    iteratedFirstChernClassCap delta X 0 L = AddMonoidHom.id _ := sorry

/-- Iteration over a successor family first caps with its last factor and then
iterates over the initial family. -/
theorem iteratedFirstChernClassCap_succ
    {S : Scheme.{u}} [UniversallyCatenary S] (delta : S → ℤ) [IsDimensionFunction delta]
    (X : Over S) [LocallyOfFiniteType X.hom] (d : ℕ)
    (L : Fin (d + 1) → X.left.Modules)
    [∀ j : Fin (d + 1), Scheme.Modules.Invertible (L j)] :
    iteratedFirstChernClassCap delta X (d + 1) L =
      (iteratedFirstChernClassCap delta X d (fun j ↦ L j.castSucc)).comp
        ((AddEquiv.cast
          ((congrArg (fun n : ℤ ↦ n - 1) (Nat.cast_succ d)).trans
            (add_sub_cancel_right (d : ℤ) 1)) :
          @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction delta) inferInstance
              (((d + 1 : ℕ) : ℤ) - 1) ≃+
            @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction delta) inferInstance (d : ℤ)).toAddMonoidHom.comp
          (firstChernClassCap delta X (L (Fin.last d)) ((d + 1 : ℕ) : ℤ))) := sorry

/-- Successively cap a degree-`k + d` Chow class with the first Chern classes of a
`Fin d`-family of invertible modules, ending in degree `k`. -/
noncomputable def iteratedFirstChernClassCapAt
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ) (d : ℕ)
    (L : Fin d → X.left.Modules)
    [invertible : ∀ j : Fin d, Scheme.Modules.Invertible (L j)] :
    @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance (k + (d : ℤ)) →+
      @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance k :=
  let rec go :
      (n : ℕ) → (M : Fin n → X.left.Modules) →
        (∀ j : Fin n, Scheme.Modules.Invertible (M j)) →
        @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction δ) inferInstance (k + (n : ℤ)) →+
          @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (X.hom.relativeDimensionFunction δ) inferInstance k
    | 0, _, _ =>
        (@reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance
          (k + (0 : ℤ)) k (add_zero k)).toAddMonoidHom
    | n + 1, M, hM =>
        (go n (fun j ↦ M j.castSucc) (fun j ↦ hM j.castSucc)).comp
          ((AddEquiv.cast
            ((congrArg (fun m : ℤ ↦ k + m - 1) (Nat.cast_succ n)).trans
              ((congrArg (fun m : ℤ ↦ m - 1)
                (add_assoc k (n : ℤ) 1).symm).trans
                (add_sub_cancel_right (k + (n : ℤ)) 1))) :
            @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                (X.hom.relativeDimensionFunction δ) inferInstance
                ((k + ((n + 1 : ℕ) : ℤ)) - 1) ≃+
              @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
                (X.hom.relativeDimensionFunction δ) inferInstance
                (k + (n : ℤ))).toAddMonoidHom.comp
            (@firstChernClassCap S _ δ _ X _ (M (Fin.last n)) (hM (Fin.last n))
              (k + ((n + 1 : ℕ) : ℤ))))
  go d L invertible

/-- The empty family acts identically on degree-`k` Chow classes. -/
theorem iteratedFirstChernClassCapAt_zero
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ)
    (L : Fin 0 → X.left.Modules)
    [∀ j : Fin 0, Scheme.Modules.Invertible (L j)] :
    iteratedFirstChernClassCapAt δ X k 0 L =
      (@reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (X.hom.relativeDimensionFunction δ) inferInstance
        (k + (0 : ℤ)) k (add_zero k)).toAddMonoidHom := sorry

/-- Iteration over a successor family first caps with its last factor and then uses the
initial family. -/
theorem iteratedFirstChernClassCapAt_succ
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (k : ℤ) (d : ℕ)
    (L : Fin (d + 1) → X.left.Modules)
    [∀ j : Fin (d + 1), Scheme.Modules.Invertible (L j)] :
    iteratedFirstChernClassCapAt δ X k (d + 1) L =
      (iteratedFirstChernClassCapAt δ X k d (fun j ↦ L j.castSucc)).comp
        ((AddEquiv.cast
          ((congrArg (fun m : ℤ ↦ k + m - 1) (Nat.cast_succ d)).trans
            ((congrArg (fun m : ℤ ↦ m - 1)
              (add_assoc k (d : ℤ) 1).symm).trans
              (add_sub_cancel_right (k + (d : ℤ)) 1))) :
          @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction δ) inferInstance
              ((k + ((d + 1 : ℕ) : ℤ)) - 1) ≃+
            @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (X.hom.relativeDimensionFunction δ) inferInstance
              (k + (d : ℤ))).toAddMonoidHom.comp
          (firstChernClassCap δ X (L (Fin.last d))
            (k + ((d + 1 : ℕ) : ℤ)))) := sorry

/-- At base degree zero, the graded iteration is the existing degree-`d` to degree-zero
first-Chern cap operation. -/
theorem iteratedFirstChernClassCapAt_zeroGrade
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X : Over S) [LocallyOfFiniteType X.hom] (d : ℕ)
    (L : Fin d → X.left.Modules)
    [∀ j : Fin d, Scheme.Modules.Invertible (L j)]
    (α : @ChowGroup X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
      (X.hom.relativeDimensionFunction δ) inferInstance (0 + (d : ℤ))) :
    iteratedFirstChernClassCapAt δ X 0 d L α =
      iteratedFirstChernClassCap δ X d L
        (@reindex X.left (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (X.hom.relativeDimensionFunction δ) inferInstance
          (0 + (d : ℤ)) (d : ℤ) (zero_add (d : ℤ)) α) := sorry

end AlgebraicGeometry.ChowGroup
