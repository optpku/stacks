/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Basic

/-!
# Morphisms of Sequential Postnikov Towers

This leaf owns componentwise tower morphisms, their identity and composition. Stage-triangle
morphisms and finite restriction are developed in separate leaves.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- A morphism of sequential Postnikov towers consists of maps on the row and auxiliary objects
which commute with the differential and the three maps of every stage triangle. -/
@[stacks 0D8Z "morphism of sequential Postnikov towers"]
structure Hom (T T' : Tower D) where
  /-- The component on the objects of the underlying row. -/
  xMap (n : ℕ) : T.X n ⟶ T'.X n
  /-- The component on auxiliary objects. -/
  yMap (n : ℕ) : T.Y n ⟶ T'.Y n
  /-- Compatibility with the differential of the underlying row. -/
  comm_d (n : ℕ) : CommSq (T.d n) (xMap (n + 1)) (xMap n) (T'.d n)
  /-- Compatibility with the comparison from an auxiliary object to the row. -/
  comm_toX (n : ℕ) : CommSq (T.toX n) (yMap n) (xMap n) (T'.toX n)
  /-- Compatibility with the second map of a stage triangle. -/
  comm_toNext (n : ℕ) :
    CommSq (T.toNext n) (xMap (n + 1)) (yMap n) (T'.toNext n)
  /-- Compatibility with the connecting map of a stage triangle. -/
  comm_connecting (n : ℕ) :
    CommSq (T.connecting n) (yMap n) ((yMap (n + 1))⟦(1 : ℤ)⟧') (T'.connecting n)

namespace Hom

variable {T T' T'' : Tower D}

/-- Construct a morphism of sequential Postnikov towers from its objectwise maps and the four
families of structural commutativity equalities. -/
@[stacks 0D8Z]
def homMk (xMap : ∀ n, T.X n ⟶ T'.X n) (yMap : ∀ n, T.Y n ⟶ T'.Y n)
    (comm_d : ∀ n, T.d n ≫ xMap n = xMap (n + 1) ≫ T'.d n)
    (comm_toX : ∀ n, T.toX n ≫ xMap n = yMap n ≫ T'.toX n)
    (comm_toNext : ∀ n, T.toNext n ≫ yMap n = xMap (n + 1) ≫ T'.toNext n)
    (comm_connecting : ∀ n, T.connecting n ≫ (yMap (n + 1))⟦(1 : ℤ)⟧' =
      yMap n ≫ T'.connecting n) :
    Hom T T' where
  xMap := xMap
  yMap := yMap
  comm_d n := ⟨comm_d n⟩
  comm_toX n := ⟨comm_toX n⟩
  comm_toNext n := ⟨comm_toNext n⟩
  comm_connecting n := ⟨comm_connecting n⟩

/-- The row-object component of `homMk` is the supplied component. -/
@[simp, stacks 0D8Z]
theorem homMk_xMap (xMap : ∀ n, T.X n ⟶ T'.X n) (yMap : ∀ n, T.Y n ⟶ T'.Y n)
    (comm_d : ∀ n, T.d n ≫ xMap n = xMap (n + 1) ≫ T'.d n)
    (comm_toX : ∀ n, T.toX n ≫ xMap n = yMap n ≫ T'.toX n)
    (comm_toNext : ∀ n, T.toNext n ≫ yMap n = xMap (n + 1) ≫ T'.toNext n)
    (comm_connecting : ∀ n, T.connecting n ≫ (yMap (n + 1))⟦(1 : ℤ)⟧' =
      yMap n ≫ T'.connecting n) (n : ℕ) :
    (homMk xMap yMap comm_d comm_toX comm_toNext comm_connecting).xMap n = xMap n := sorry

/-- The auxiliary-object component of `homMk` is the supplied component. -/
@[simp, stacks 0D8Z]
theorem homMk_yMap (xMap : ∀ n, T.X n ⟶ T'.X n) (yMap : ∀ n, T.Y n ⟶ T'.Y n)
    (comm_d : ∀ n, T.d n ≫ xMap n = xMap (n + 1) ≫ T'.d n)
    (comm_toX : ∀ n, T.toX n ≫ xMap n = yMap n ≫ T'.toX n)
    (comm_toNext : ∀ n, T.toNext n ≫ yMap n = xMap (n + 1) ≫ T'.toNext n)
    (comm_connecting : ∀ n, T.connecting n ≫ (yMap (n + 1))⟦(1 : ℤ)⟧' =
      yMap n ≫ T'.connecting n) (n : ℕ) :
    (homMk xMap yMap comm_d comm_toX comm_toNext comm_connecting).yMap n = yMap n := sorry

/-- The identity morphism of a sequential Postnikov tower. -/
@[stacks 0D8Z]
def id (T : Tower D) : Hom T T where
  xMap n := 𝟙 (T.X n)
  yMap n := 𝟙 (T.Y n)
  comm_d := sorry
  comm_toX := sorry
  comm_toNext := sorry
  comm_connecting := sorry

/-- The componentwise composite of two morphisms of sequential Postnikov towers. -/
@[stacks 0D8Z]
def comp (f : Hom T T') (g : Hom T' T'') : Hom T T'' where
  xMap n := f.xMap n ≫ g.xMap n
  yMap n := f.yMap n ≫ g.yMap n
  comm_d := sorry
  comm_toX := sorry
  comm_toNext := sorry
  comm_connecting := sorry

/-- The row-object component of an identity tower morphism is an identity. -/
@[simp]
theorem id_xMap (T : Tower D) (n : ℕ) : (id T).xMap n = 𝟙 (T.X n) := sorry

/-- The auxiliary-object component of an identity tower morphism is an identity. -/
@[simp]
theorem id_yMap (T : Tower D) (n : ℕ) : (id T).yMap n = 𝟙 (T.Y n) := sorry

/-- Row-object components of tower morphisms compose componentwise. -/
@[simp]
theorem comp_xMap (f : Hom T T') (g : Hom T' T'') (n : ℕ) :
    (comp f g).xMap n = f.xMap n ≫ g.xMap n := sorry

/-- Auxiliary-object components of tower morphisms compose componentwise. -/
@[simp]
theorem comp_yMap (f : Hom T T') (g : Hom T' T'') (n : ℕ) :
    (comp f g).yMap n = f.yMap n ≫ g.yMap n := sorry

/-- The identity tower morphism is a left identity for composition. -/
@[simp]
theorem id_comp (f : Hom T T') : comp (id T) f = f := sorry

/-- The identity tower morphism is a right identity for composition. -/
@[simp]
theorem comp_id (f : Hom T T') : comp f (id T') = f := sorry

/-- Composition of tower morphisms is associative. -/
theorem comp_assoc {T''' : Tower D} (f : Hom T T') (g : Hom T' T'')
    (h : Hom T'' T''') : comp (comp f g) h = comp f (comp g h) := sorry

/-- Tower morphisms are determined by their components on row and auxiliary objects. -/
@[ext (iff := false)]
theorem ext {f g : Hom T T'} (hX : ∀ n, f.xMap n = g.xMap n)
    (hY : ∀ n, f.yMap n = g.yMap n) : f = g := sorry

/-- Two tower morphisms are equal exactly when all their row-object and auxiliary-object
components agree. -/
@[simp, stacks 0D8Z]
theorem ext_iff {f g : Hom T T'} :
    f = g ↔ (∀ n, f.xMap n = g.xMap n) ∧ ∀ n, f.yMap n = g.yMap n := sorry

/-- The differential square of a tower morphism as an equality. -/
@[reassoc]
theorem comm_d_w (f : Hom T T') (n : ℕ) :
    T.d n ≫ f.xMap n = f.xMap (n + 1) ≫ T'.d n := sorry

/-- The comparison square of a tower morphism as an equality. -/
@[reassoc]
theorem comm_toX_w (f : Hom T T') (n : ℕ) :
    T.toX n ≫ f.xMap n = f.yMap n ≫ T'.toX n := sorry

/-- The second-map square of a tower morphism as an equality. -/
@[reassoc]
theorem comm_toNext_w (f : Hom T T') (n : ℕ) :
    T.toNext n ≫ f.yMap n = f.xMap (n + 1) ≫ T'.toNext n := sorry

/-- The connecting-map square of a tower morphism as an equality. -/
@[reassoc]
theorem comm_connecting_w (f : Hom T T') (n : ℕ) :
    T.connecting n ≫ (f.yMap (n + 1))⟦(1 : ℤ)⟧' =
      f.yMap n ≫ T'.connecting n := sorry

attribute [simp] comm_d_w_assoc comm_toX_w_assoc comm_toNext_w_assoc comm_connecting_w_assoc

end Hom
end CategoryTheory.PostnikovSystem.Tower
