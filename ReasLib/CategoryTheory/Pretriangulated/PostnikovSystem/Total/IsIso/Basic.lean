/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Iso.Explicit
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Basic

/-!
# Componentwise Isomorphisms in the Total Postnikov-System Category

This file constructs explicit inverses and isomorphisms from invertibility of
the finite-row map and every auxiliary-object component.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Total

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {n : ℕ} {P Q : Total D n}

/-- Compatibility of componentwise inverses with the maps from auxiliary objects to row
objects. -/
@[stacks 0D7Z]
theorem inverse_comm_toX (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) (i : Fin (n + 1)) :
    CommSq (Q.system.toX i) (hy i).toIso.inv
      (hbase.toIso.inv.app i) (P.system.toX i) := sorry

/-- Compatibility of componentwise inverses with the second maps of stage triangles. -/
@[stacks 0D7Z]
theorem inverse_comm_toNext (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) (i : Fin n) :
    CommSq (Q.system.toNext i) (hbase.toIso.inv.app i.castSucc)
      (hy i.succ).toIso.inv
      (P.system.toNext i) := sorry

/-- Compatibility of componentwise inverses with the connecting maps of stage triangles. -/
@[stacks 0D7Z]
theorem inverse_comm_connecting (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) (i : Fin n) :
    CommSq (Q.system.connecting i)
      (hy i.succ).toIso.inv
      (((hy i.castSucc).toIso.inv)⟦(1 : ℤ)⟧')
      (P.system.connecting i) := sorry

/-- The componentwise inverse of a morphism in the total category. Invertibility certificates
are explicit inputs, so this construction does not require downstream `letI` declarations. -/
@[stacks 0D7Z "componentwise inverse of a total Postnikov-system morphism"]
noncomputable def inverse (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) : Q ⟶ P where
  base := hbase.toIso.inv
  systemMap :=
    { yMap := fun i ↦ (hy i).toIso.inv
      comm_toX := inverse_comm_toX f hbase hy
      comm_toNext := inverse_comm_toNext f hbase hy
      comm_connecting := inverse_comm_connecting f hbase hy }

/-- The base component of the componentwise inverse is the inverse finite-row map. -/
@[simp, stacks 0D7Z]
theorem inverse_base (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) :
    (inverse f hbase hy).base = hbase.toIso.inv := sorry

/-- Each auxiliary component of the componentwise inverse is the corresponding inverse map. -/
@[simp, stacks 0D7Z]
theorem inverse_yMap (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) (i : Fin (n + 1)) :
    (inverse f hbase hy).systemMap.yMap i =
      (hy i).toIso.inv := sorry

/-- A total morphism followed by its componentwise inverse is the identity. -/
@[simp, stacks 0D7Z]
theorem hom_inverse_id (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) :
    f ≫ inverse f hbase hy = 𝟙 P := sorry

/-- The componentwise inverse followed by the original total morphism is the identity. -/
@[simp, stacks 0D7Z]
theorem inverse_hom_id (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) :
    inverse f hbase hy ≫ f = 𝟙 Q := sorry

/-- Assemble an isomorphism in the total category from invertibility of the base and all
auxiliary-object components. -/
@[stacks 0D7Z "componentwise isomorphism in the total Postnikov-system category"]
noncomputable def isoOfComponents (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) : P ≅ Q where
  hom := f
  inv := inverse f hbase hy
  hom_inv_id := hom_inverse_id f hbase hy
  inv_hom_id := inverse_hom_id f hbase hy

/-- The forward map of `isoOfComponents` is the original total morphism. -/
@[simp, stacks 0D7Z]
theorem isoOfComponents_hom (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) :
    (isoOfComponents f hbase hy).hom = f := sorry

/-- The inverse map of `isoOfComponents` is the explicit componentwise inverse. -/
@[simp, stacks 0D7Z]
theorem isoOfComponents_inv (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) :
    (isoOfComponents f hbase hy).inv = inverse f hbase hy := sorry

/-- Componentwise invertibility implies invertibility in the total category. This is a theorem,
not a global instance, to avoid a typeclass loop with functors mapping total isomorphisms to their
components. -/
@[stacks 0D7Z]
theorem isIso_of_components (f : P ⟶ Q) (hbase : IsIso f.base)
    (hy : ∀ i, IsIso (f.systemMap.yMap i)) : IsIso f := sorry

/-- A total morphism is invertible exactly when its base and all auxiliary-object components are
invertible. -/
@[stacks 0D7Z "componentwise criterion for total Postnikov-system isomorphisms"]
theorem isIso_iff (f : P ⟶ Q) :
    IsIso f ↔ IsIso f.base ∧ ∀ i, IsIso (f.systemMap.yMap i) := sorry

/-- An isomorphism in the total category is invertible on every auxiliary-object component. -/
@[stacks 0D7Z]
instance yMapIsIso (f : P ⟶ Q) [IsIso f] (i : Fin (n + 1)) :
    IsIso (f.systemMap.yMap i) := sorry

/-- The base component of an invertible total morphism is invertible. -/
@[stacks 0D7Z]
instance baseIsIso (f : P ⟶ Q) [IsIso f] : IsIso f.base := sorry

end CategoryTheory.PostnikovSystem.Total
