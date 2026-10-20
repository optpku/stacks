/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Action
public import Mathlib.LinearAlgebra.BilinearMap
public import ReasLib.RingTheory.Algebra.FreeDimensional.UnitFixing
public import ReasLib.AlgebraicGeometry.FreeDimensionalAlgebra

/-!
# Action groupoid of unit-fixing automorphisms on free algebras

Conjugation of bilinear multiplication defines a right action of `glFixOne R d`,
realized as a left action of the opposite group. Algebra arrows retain their
ordinary matrix coordinates and contravariant multiplication intertwiners.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FreeDimAlgebra

variable {R : Type u} [CommRing R] {d : ℕ} [NeZero d]

private theorem conjugate_laws (g : glFixOne R d) (m : FreeDimAlgebra R d) :
    let b := (m.mul.compl₁₂ g.val.val g.val.val).compr₂ g.val.inv
    (∀ x y z, b (b x y) z = b x (b y z)) ∧
    (∀ x y, b x y = b y x) ∧ (∀ x, b (one R d) x = x) := sorry

/-- Conjugation of a free `d`-dimensional algebra by a unit-fixing automorphism:
the multiplication of `conjugate g m` is `g⁻¹ ∘ m.mul ∘ (g ⊗ g)`. -/
def conjugate (g : glFixOne R d) (m : FreeDimAlgebra R d) : FreeDimAlgebra R d :=
  FreeDimAlgebra.ofMul ((m.mul.compl₁₂ g.val.val g.val.val).compr₂ g.val.inv)
    (conjugate_laws g m).1 (conjugate_laws g m).2.1 (conjugate_laws g m).2.2

/-- The multiplication of `conjugate g m` is `g⁻¹ ∘ m.mul ∘ (g ⊗ g)`. -/
theorem conjugate_mul (g : glFixOne R d) (m : FreeDimAlgebra R d) (x y : Fin d → R) :
    (conjugate g m).mul x y = g.val.inv (m.mul (g.val.val x) (g.val.val y)) :=
  by rfl

private theorem conjugate_action_laws :
    (∀ m : FreeDimAlgebra R d, conjugate 1 m = m) ∧
    (∀ (g h : glFixOne R d) (m : FreeDimAlgebra R d),
      conjugate (g * h) m = conjugate h (conjugate g m)) := sorry

/-- The opposite group acts by `g • m = g.unop⁻¹ ∘ m ∘ (g.unop ⊗ g.unop)`. -/
instance instMulActionFreeDimAlgebra : MulAction (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) where
  smul g m := conjugate g.unop m
  one_smul := conjugate_action_laws.1
  mul_smul g h m := conjugate_action_laws.2 h.unop g.unop m

/-- The action of `g` on `m` is conjugation of multiplication. -/
theorem smul_def (g : glFixOne R d) (m : FreeDimAlgebra R d) :
    MulOpposite.op g • m = conjugate g m := by rfl

end FreeDimAlgebra

namespace FA

private theorem toAction_map_property {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    {m m' : FreeDimAlgebra R d} (φ : m ⟶ m') :
    FreeDimAlgebra.conjugate ⟨φ.equiv, φ.map_one⟩ m = m' := sorry

private theorem toAction_laws (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    let objMap : FreeDimAlgebra R d →
        ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) := fun m ↦ m
    let arrowMap : ∀ {m m' : FreeDimAlgebra R d}, (m ⟶ m') →
        (objMap m ⟶ objMap m') :=
      fun φ ↦ ⟨MulOpposite.op ⟨φ.equiv, φ.map_one⟩, toAction_map_property φ⟩
    (∀ m, arrowMap (𝟙 m) = 𝟙 (objMap m)) ∧
    (∀ (m₁ m₂ m₃ : FreeDimAlgebra R d) (φ : m₁ ⟶ m₂) (ψ : m₂ ⟶ m₃),
      arrowMap (φ ≫ ψ) = arrowMap φ ≫ arrowMap ψ) := sorry

/-- The fibre functor sending a free `d`-dimensional algebra to the corresponding
object of the action groupoid. -/
def toAction (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    FreeDimAlgebra R d ⥤ ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) where
  obj m := (m : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d))
  map φ := ⟨MulOpposite.op ⟨φ.equiv, φ.map_one⟩, toAction_map_property φ⟩
  map_id := (toAction_laws R d).1
  map_comp := (toAction_laws R d).2 _ _ _

/-- `toAction` is the identity on the underlying free algebras. -/
theorem toAction_obj {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (m : FreeDimAlgebra R d) :
    ActionCategory.back ((toAction R d).obj m) = m := by rfl

private theorem fromAction_map_property {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    {m m' : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d)} (f : m ⟶ m') :
    ∀ x y, (ActionCategory.back m).mul ((MulOpposite.unop f.val).val.val x)
      ((MulOpposite.unop f.val).val.val y) =
      (MulOpposite.unop f.val).val.val ((ActionCategory.back m').mul x y) := sorry

private theorem fromAction_laws (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    let arrowMap : ∀ {m m' : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d)},
        (m ⟶ m') → (ActionCategory.back m ⟶ ActionCategory.back m') :=
      fun f ↦ FreeDimAlgebra.Hom.of (MulOpposite.unop f.val).val
        (MulOpposite.unop f.val).property (fromAction_map_property f)
    (∀ m, arrowMap (𝟙 m) = 𝟙 (ActionCategory.back m)) ∧
    (∀ (m₁ m₂ m₃ : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d))
      (φ : m₁ ⟶ m₂) (ψ : m₂ ⟶ m₃),
      arrowMap (φ ≫ ψ) = arrowMap φ ≫ arrowMap ψ) := sorry

/-- The inverse fibre functor, recovering a free `d`-dimensional algebra from an
object of the action groupoid. -/
def fromAction (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) ⥤ FreeDimAlgebra R d where
  obj := ActionCategory.back
  map f := FreeDimAlgebra.Hom.of (MulOpposite.unop f.val).val
    (MulOpposite.unop f.val).property (fromAction_map_property f)
  map_id := (fromAction_laws R d).1
  map_comp := (fromAction_laws R d).2 _ _ _

/-- `fromAction` is `ActionCategory.back` on objects. -/
theorem fromAction_obj {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (m : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d)) :
    (fromAction R d).obj m = ActionCategory.back m := by rfl

private theorem mapAction_map_property {R S : Type u} [CommRing R] [CommRing S]
    {d : ℕ} [NeZero d] (f : R →+* S)
    {m m' : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d)} (φ : m ⟶ m') :
    FreeDimAlgebra.conjugate (GLFixOne.map f (MulOpposite.unop φ.val))
      (FreeDimAlgebra.baseChange f (ActionCategory.back m)) =
      FreeDimAlgebra.baseChange f (ActionCategory.back m') := sorry

private theorem mapAction_laws {R S : Type u} [CommRing R] [CommRing S]
    {d : ℕ} [NeZero d] (f : R →+* S) :
    let objMap : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) →
        ActionCategory (glFixOne S d)ᵐᵒᵖ (FreeDimAlgebra S d) :=
      fun m ↦ FreeDimAlgebra.baseChange f (ActionCategory.back m)
    let arrowMap : ∀ {m m' : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d)},
        (m ⟶ m') → (objMap m ⟶ objMap m') :=
      fun φ ↦ ⟨MulOpposite.op (GLFixOne.map f (MulOpposite.unop φ.val)),
        mapAction_map_property f φ⟩
    (∀ m, arrowMap (𝟙 m) = 𝟙 (objMap m)) ∧
    (∀ (m₁ m₂ m₃ : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d))
      (φ : m₁ ⟶ m₂) (ψ : m₂ ⟶ m₃),
      arrowMap (φ ≫ ψ) = arrowMap φ ≫ arrowMap ψ) := sorry

/-- Base change of rings induces a functor of action groupoids. -/
def mapAction {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d] (f : R →+* S) :
    ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d) ⥤
      ActionCategory (glFixOne S d)ᵐᵒᵖ (FreeDimAlgebra S d) where
  obj m :=
    (FreeDimAlgebra.baseChange f (ActionCategory.back m) :
      ActionCategory (glFixOne S d)ᵐᵒᵖ (FreeDimAlgebra S d))
  map φ := ⟨MulOpposite.op (GLFixOne.map f (MulOpposite.unop φ.val)),
    mapAction_map_property f φ⟩
  map_id := (mapAction_laws f).1
  map_comp := (mapAction_laws f).2 _ _ _

/-- On objects, `mapAction f` is base change of the underlying free algebra. -/
theorem mapAction_obj {R S : Type u} [CommRing R] [CommRing S] {d : ℕ} [NeZero d]
    (f : R →+* S) (m : ActionCategory (glFixOne R d)ᵐᵒᵖ (FreeDimAlgebra R d)) :
    ActionCategory.back ((mapAction f).obj m) =
      FreeDimAlgebra.baseChange f (ActionCategory.back m) := by rfl


private theorem homEquiv_laws {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (m m' : FreeDimAlgebra R d) :
    let forward : (m ⟶ m') → {g : glFixOne R d // FreeDimAlgebra.conjugate g m = m'} :=
      fun φ ↦ ⟨⟨φ.equiv, φ.map_one⟩, toAction_map_property φ⟩
    let backward : {g : glFixOne R d // FreeDimAlgebra.conjugate g m = m'} → (m ⟶ m') :=
      fun g ↦ FreeDimAlgebra.Hom.of g.1.val g.1.property
        (fromAction_map_property (m := (m : ActionCategory (glFixOne R d)ᵐᵒᵖ
          (FreeDimAlgebra R d))) (m' := (m' : ActionCategory (glFixOne R d)ᵐᵒᵖ
          (FreeDimAlgebra R d))) ⟨MulOpposite.op g.1, g.property⟩)
    Function.LeftInverse backward forward ∧ Function.RightInverse backward forward := sorry

/-- An algebra arrow is encoded by its unit-fixing automorphism and target equation. -/
def homEquiv {R : Type u} [CommRing R] {d : ℕ} [NeZero d] (m m' : FreeDimAlgebra R d) :
    (m ⟶ m') ≃ {g : glFixOne R d // FreeDimAlgebra.conjugate g m = m'} where
  toFun φ := ⟨⟨φ.equiv, φ.map_one⟩, toAction_map_property φ⟩
  invFun g := FreeDimAlgebra.Hom.of g.1.val g.1.property
    (fromAction_map_property (m := (m : ActionCategory (glFixOne R d)ᵐᵒᵖ
      (FreeDimAlgebra R d))) (m' := (m' : ActionCategory (glFixOne R d)ᵐᵒᵖ
      (FreeDimAlgebra R d))) ⟨MulOpposite.op g.1, g.property⟩)
  left_inv := (homEquiv_laws m m').1
  right_inv := (homEquiv_laws m m').2

/-- The equivalence label of an algebra arrow is its underlying automorphism. -/
theorem homEquiv_apply {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    {m m' : FreeDimAlgebra R d} (φ : m ⟶ m') :
    (homEquiv m m' φ).1.val = φ.equiv := rfl

private theorem arrowEquiv_laws (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    let forward : glFixOne R d × FreeDimAlgebra R d →
        (Σ m : FreeDimAlgebra R d, Σ m' : FreeDimAlgebra R d, m ⟶ m') :=
      fun p ↦ ⟨p.2, FreeDimAlgebra.conjugate p.1 p.2,
        (homEquiv p.2 (FreeDimAlgebra.conjugate p.1 p.2)).symm ⟨p.1, rfl⟩⟩
    let backward : (Σ m : FreeDimAlgebra R d, Σ m' : FreeDimAlgebra R d, m ⟶ m') →
        glFixOne R d × FreeDimAlgebra R d :=
      fun p ↦ ⟨(homEquiv p.1 p.2.1) p.2.2, p.1⟩
    Function.LeftInverse backward forward ∧ Function.RightInverse backward forward := sorry

/-- The total arrow equivalence records a unit-fixing label and source object. -/
def arrowEquiv (R : Type u) [CommRing R] (d : ℕ) [NeZero d] :
    glFixOne R d × FreeDimAlgebra R d ≃
      (Σ m : FreeDimAlgebra R d, Σ m' : FreeDimAlgebra R d, m ⟶ m') where
  toFun p := ⟨p.2, FreeDimAlgebra.conjugate p.1 p.2,
    (homEquiv p.2 (FreeDimAlgebra.conjugate p.1 p.2)).symm ⟨p.1, rfl⟩⟩
  invFun p := ⟨(homEquiv p.1 p.2.1) p.2.2, p.1⟩
  left_inv := (arrowEquiv_laws R d).1
  right_inv := (arrowEquiv_laws R d).2

/-- The source of the arrow coordinate is the second component. -/
theorem arrowEquiv_source {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (g : glFixOne R d) (m : FreeDimAlgebra R d) :
    (arrowEquiv R d (g, m)).1 = m := by rfl

/-- The target of the arrow coordinate is the conjugated algebra. -/
theorem arrowEquiv_target {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    (g : glFixOne R d) (m : FreeDimAlgebra R d) :
    (arrowEquiv R d (g, m)).2.1 = FreeDimAlgebra.conjugate g m := by rfl


/-- Underlying automorphisms multiply in the order induced by arrow composition. -/
theorem homEquiv_comp {R : Type u} [CommRing R] {d : ℕ} [NeZero d]
    {m₁ m₂ m₃ : FreeDimAlgebra R d} (φ : m₁ ⟶ m₂) (ψ : m₂ ⟶ m₃) :
    (homEquiv m₁ m₃ (φ ≫ ψ)).val =
      (homEquiv m₁ m₂ φ).val * (homEquiv m₂ m₃ ψ).val := by
  apply Subtype.ext
  exact FreeDimAlgebra.Hom.comp_equiv φ ψ


end FA

end AlgebraicGeometry
