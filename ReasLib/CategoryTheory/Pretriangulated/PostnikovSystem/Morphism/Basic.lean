/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Stages.Maps
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Morphisms of Finite Postnikov Systems

This file defines compatible maps between finite Postnikov systems and their
identity, composition, extensionality, and componentwise commutation API.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- A morphism of Postnikov systems over a morphism of their finite rows. It records stagewise
maps on auxiliary objects and their compatibility with all three maps in every stage triangle. -/
@[stacks 0D7Z "morphism of Postnikov systems"]
structure PostnikovSystem.Morphism {n : ℕ} {X X' : ComposableArrows D n}
    (P : PostnikovSystem X) (P' : PostnikovSystem X') (φ : X ⟶ X') where
  /-- The stagewise map between auxiliary objects. -/
  yMap (i : Fin (n + 1)) : P i ⟶ P' i
  /-- Compatibility with the maps from auxiliary objects to row objects. -/
  comm_toX (i : Fin (n + 1)) : CommSq (P.toX i) (yMap i) (φ.app i) (P'.toX i)
  /-- Compatibility with the second maps of stage triangles. -/
  comm_toNext (i : Fin n) :
    CommSq (P.toNext i) (φ.app i.castSucc) (yMap i.succ) (P'.toNext i)
  /-- Compatibility with the connecting maps of stage triangles. -/
  comm_connecting (i : Fin n) :
    CommSq (P.connecting i) (yMap i.succ) ((yMap i.castSucc)⟦(1 : ℤ)⟧') (P'.connecting i)

namespace PostnikovSystem.Morphism

variable {n : ℕ} {X X' : ComposableArrows D n}
variable {P : PostnikovSystem X} {P' : PostnikovSystem X'} {φ : X ⟶ X'}

/-- Construct a morphism of Postnikov systems from its auxiliary-object maps and the three
families of stagewise commutativity equalities. -/
@[stacks 0D7Z]
def homMk (yMap : ∀ i : Fin (n + 1), P i ⟶ P' i)
    (comm_toX : ∀ i, P.toX i ≫ φ.app i = yMap i ≫ P'.toX i)
    (comm_toNext : ∀ i, P.toNext i ≫ yMap i.succ = φ.app i.castSucc ≫ P'.toNext i)
    (comm_connecting : ∀ i, P.connecting i ≫ (yMap i.castSucc)⟦(1 : ℤ)⟧' =
      yMap i.succ ≫ P'.connecting i) :
    PostnikovSystem.Morphism P P' φ where
  yMap := yMap
  comm_toX i := ⟨comm_toX i⟩
  comm_toNext i := ⟨comm_toNext i⟩
  comm_connecting i := ⟨comm_connecting i⟩

/-- The auxiliary-object component of `homMk` is the supplied component. -/
@[simp, stacks 0D7Z]
theorem homMk_yMap (yMap : ∀ i : Fin (n + 1), P i ⟶ P' i)
    (comm_toX : ∀ i, P.toX i ≫ φ.app i = yMap i ≫ P'.toX i)
    (comm_toNext : ∀ i, P.toNext i ≫ yMap i.succ = φ.app i.castSucc ≫ P'.toNext i)
    (comm_connecting : ∀ i, P.connecting i ≫ (yMap i.castSucc)⟦(1 : ℤ)⟧' =
      yMap i.succ ≫ P'.connecting i) (i : Fin (n + 1)) :
    (homMk yMap comm_toX comm_toNext comm_connecting).yMap i = yMap i := sorry

/-- The identity morphism of a Postnikov system. -/
@[stacks 0D7Z]
def id (P : PostnikovSystem X) :
    PostnikovSystem.Morphism P P (𝟙 X) where
  yMap i := 𝟙 (P i)
  comm_toX := sorry
  comm_toNext := sorry
  comm_connecting := sorry

/-- Compose compatible morphisms of Postnikov systems. -/
@[stacks 0D7Z]
def comp {X'' : ComposableArrows D n} {P'' : PostnikovSystem X''} {φ' : X' ⟶ X''}
    (ψ : PostnikovSystem.Morphism P P' φ) (χ : PostnikovSystem.Morphism P' P'' φ') :
    PostnikovSystem.Morphism P P'' (φ ≫ φ') where
  yMap i := ψ.yMap i ≫ χ.yMap i
  comm_toX := sorry
  comm_toNext := sorry
  comm_connecting := sorry

/-- The auxiliary-object map of the identity Postnikov-system morphism is the identity. -/
@[simp, stacks 0D7Z]
theorem id_yMap (P : PostnikovSystem X) (i : Fin (n + 1)) :
    (id P).yMap i = 𝟙 (P i) := sorry

/-- The auxiliary-object map of a composite is the componentwise composite. -/
@[simp, stacks 0D7Z]
theorem comp_yMap {X'' : ComposableArrows D n} {P'' : PostnikovSystem X''} {φ' : X' ⟶ X''}
    (ψ : PostnikovSystem.Morphism P P' φ) (χ : PostnikovSystem.Morphism P' P'' φ')
    (i : Fin (n + 1)) :
    (comp ψ χ).yMap i = ψ.yMap i ≫ χ.yMap i := sorry

/-- A morphism of Postnikov systems is determined by its maps on auxiliary objects. -/
@[stacks 0D7Z, ext (iff := false)]
theorem ext {ψ ψ' : PostnikovSystem.Morphism P P' φ}
    (h : ∀ i, ψ.yMap i = ψ'.yMap i) :
    ψ = ψ' := sorry

/-- Two morphisms of Postnikov systems agree exactly when all their auxiliary-object
components agree. -/
@[simp, stacks 0D7Z]
theorem ext_iff {ψ ψ' : PostnikovSystem.Morphism P P' φ} :
    ψ = ψ' ↔ ∀ i, ψ.yMap i = ψ'.yMap i := sorry

/-- The maps from auxiliary objects to the finite rows commute with a system morphism. -/
@[reassoc, stacks 0D7Z]
theorem comm_toX_w (ψ : PostnikovSystem.Morphism P P' φ) (i : Fin (n + 1)) :
    P.toX i ≫ φ.app i = ψ.yMap i ≫ P'.toX i := sorry

/-- The second maps of the stage triangles commute with a system morphism. -/
@[reassoc, stacks 0D7Z]
theorem comm_toNext_w (ψ : PostnikovSystem.Morphism P P' φ) (i : Fin n) :
    P.toNext i ≫ ψ.yMap i.succ = φ.app i.castSucc ≫ P'.toNext i := sorry

/-- The connecting maps of the stage triangles commute with a system morphism. -/
@[reassoc, stacks 0D7Z]
theorem comm_connecting_w (ψ : PostnikovSystem.Morphism P P' φ) (i : Fin n) :
    P.connecting i ≫ (ψ.yMap i.castSucc)⟦(1 : ℤ)⟧' =
      ψ.yMap i.succ ≫ P'.connecting i := sorry

attribute [simp] PostnikovSystem.Morphism.comm_toX_w_assoc
attribute [simp] PostnikovSystem.Morphism.comm_toNext_w_assoc
attribute [simp] PostnikovSystem.Morphism.comm_connecting_w_assoc

end PostnikovSystem.Morphism

end

end CategoryTheory
