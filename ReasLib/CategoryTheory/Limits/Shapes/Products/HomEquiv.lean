/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 016R

# Hom equivalences for indexed products and coproducts

This file packages the universal properties of indexed products and coproducts as Hom
equivalences. Binary products and coproducts are derived through the walking-pair specialization.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.Limits

namespace pairFunction

variable {C : Type u} [Category.{v} C]

/-- A chosen binary product supplies the same product viewed as a `WalkingPair`-indexed
family. -/
@[stacks 016R "binary products as walking-pair indexed products",
  stacks 0170 "binary products as walking-pair indexed products"]
instance hasProduct (X Y : C) [HasBinaryProduct X Y] :
    HasProduct (pairFunction X Y) :=
  inferInstanceAs (HasLimit (pair X Y))

/-- A chosen binary coproduct supplies the same coproduct viewed as a `WalkingPair`-indexed
family. -/
@[stacks 04AN "binary coproducts as walking-pair indexed coproducts"]
instance hasCoproduct (X Y : C) [HasBinaryCoproduct X Y] :
    HasCoproduct (pairFunction X Y) :=
  inferInstanceAs (HasColimit (pair X Y))

end pairFunction

namespace WalkingPair

/-- Dependent functions on `WalkingPair` are equivalent to pairs of their left and right
values. -/
@[stacks 016R "walking-pair dependent functions",
  stacks 0170 "walking-pair dependent functions"]
def piEquiv (F : WalkingPair → Type w) :
    ((j : WalkingPair) → F j) ≃ F left × F right where
  toFun f := (f left, f right)
  invFun p j := WalkingPair.casesOn j p.1 p.2
  left_inv := sorry
  right_inv := sorry

namespace piEquiv

/-- The walking-pair equivalence evaluates a dependent function at the two points. -/
@[simp, stacks 016R "walking-pair equivalence application",
  stacks 0170 "walking-pair equivalence application"]
theorem apply (F : WalkingPair → Type w) (f : (j : WalkingPair) → F j) :
    piEquiv F f = (f left, f right) := sorry

/-- The inverse walking-pair equivalence has the prescribed left value. -/
@[simp, stacks 016R "left value of the inverse walking-pair equivalence",
  stacks 0170 "left value of the inverse walking-pair equivalence"]
theorem symm_apply_left (F : WalkingPair → Type w) (p : F left × F right) :
    (piEquiv F).symm p left = p.1 := sorry

/-- The inverse walking-pair equivalence has the prescribed right value. -/
@[simp, stacks 016R "right value of the inverse walking-pair equivalence",
  stacks 0170 "right value of the inverse walking-pair equivalence"]
theorem symm_apply_right (F : WalkingPair → Type w) (p : F left × F right) :
    (piEquiv F).symm p right = p.2 := sorry

end piEquiv

end WalkingPair

namespace Pi

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} (X : ι → C) [HasProduct X]

/-- Morphisms to an indexed product are equivalent to families of morphisms to its factors. -/
@[stacks 016R "universal property of indexed products as a Hom equivalence",
  stacks 0170 "universal property of indexed products as a Hom equivalence"]
noncomputable def homEquiv (W : C) :
    (W ⟶ ∏ᶜ X) ≃ ((i : ι) → W ⟶ X i) where
  toFun h i := h ≫ Pi.π X i
  invFun p := Pi.lift p
  left_inv := sorry
  right_inv := sorry

namespace homEquiv

/-- The indexed-product Hom equivalence is the family of projection composites. -/
@[simp, stacks 016R "indexed-product Hom equivalence application",
  stacks 0170 "indexed-product Hom equivalence application"]
theorem apply {W : C} (h : W ⟶ ∏ᶜ X) :
    homEquiv X W h = fun i ↦ h ≫ Pi.π X i := sorry

/-- A coordinate of the indexed-product Hom equivalence is the corresponding projection
composite. -/
@[simp, stacks 016R "coordinate of the indexed-product Hom equivalence",
  stacks 0170 "coordinate of the indexed-product Hom equivalence"]
theorem apply_apply {W : C} (h : W ⟶ ∏ᶜ X) (i : ι) :
    homEquiv X W h i = h ≫ Pi.π X i := sorry

/-- The inverse indexed-product Hom equivalence is the canonical product lift. -/
@[simp, stacks 016R "inverse of the indexed-product Hom equivalence",
  stacks 0170 "inverse of the indexed-product Hom equivalence"]
theorem symm_apply {W : C} (p : (i : ι) → W ⟶ X i) :
    (homEquiv X W).symm p = Pi.lift p := sorry

/-- The indexed-product Hom equivalence is natural under precomposition. -/
@[simp, stacks 016R "naturality of the indexed-product Hom equivalence",
  stacks 0170 "naturality of the indexed-product Hom equivalence"]
theorem precomp {V W : C} (k : V ⟶ W) (h : W ⟶ ∏ᶜ X) :
    homEquiv X V (k ≫ h) = fun i ↦ k ≫ homEquiv X W h i := sorry

/-- The inverse indexed-product Hom equivalence commutes with precomposition. -/
@[stacks 016R "inverse naturality of the indexed-product Hom equivalence",
  stacks 0170 "inverse naturality of the indexed-product Hom equivalence"]
theorem symm_precomp {V W : C} (k : V ⟶ W) (p : (i : ι) → W ⟶ X i) :
    (homEquiv X V).symm (fun i ↦ k ≫ p i) =
      k ≫ (homEquiv X W).symm p := sorry

end homEquiv

end Pi

namespace Sigma

variable {C : Type u} [Category.{v} C]
variable {ι : Type w} (X : ι → C) [HasCoproduct X]

/-- Morphisms from an indexed coproduct are equivalent to families of morphisms from its
factors. -/
@[stacks 04AN "universal property of indexed coproducts as a Hom equivalence"]
noncomputable def homEquiv (W : C) :
    (∐ X ⟶ W) ≃ ((i : ι) → X i ⟶ W) where
  toFun h i := Sigma.ι X i ≫ h
  invFun p := Sigma.desc p
  left_inv := sorry
  right_inv := sorry

namespace homEquiv

/-- The indexed-coproduct Hom equivalence is the family of inclusion composites. -/
@[simp, stacks 04AN "indexed-coproduct Hom equivalence application"]
theorem apply {W : C} (h : ∐ X ⟶ W) :
    homEquiv X W h = fun i ↦ Sigma.ι X i ≫ h := sorry

/-- A coordinate of the indexed-coproduct Hom equivalence is the corresponding inclusion
composite. -/
@[simp, stacks 04AN "coordinate of the indexed-coproduct Hom equivalence"]
theorem apply_apply {W : C} (h : ∐ X ⟶ W) (i : ι) :
    homEquiv X W h i = Sigma.ι X i ≫ h := sorry

/-- The inverse indexed-coproduct Hom equivalence is the canonical coproduct descent. -/
@[simp, stacks 04AN "inverse of the indexed-coproduct Hom equivalence"]
theorem symm_apply {W : C} (p : (i : ι) → X i ⟶ W) :
    (homEquiv X W).symm p = Sigma.desc p := sorry

/-- The indexed-coproduct Hom equivalence is natural under postcomposition. -/
@[simp, stacks 04AN "naturality of the indexed-coproduct Hom equivalence"]
theorem postcomp {V W : C} (h : ∐ X ⟶ V) (k : V ⟶ W) :
    homEquiv X W (h ≫ k) = fun i ↦ homEquiv X V h i ≫ k := sorry

/-- The inverse indexed-coproduct Hom equivalence commutes with postcomposition. -/
@[stacks 04AN "inverse naturality of the indexed-coproduct Hom equivalence"]
theorem symm_postcomp {V W : C} (p : (i : ι) → X i ⟶ V) (k : V ⟶ W) :
    (homEquiv X W).symm (fun i ↦ p i ≫ k) =
      (homEquiv X V).symm p ≫ k := sorry

end homEquiv

end Sigma

namespace prod

variable {C : Type u} [Category.{v} C]
variable (X Y : C) [HasBinaryProduct X Y]

/-- Morphisms to a binary product are equivalent to pairs of morphisms to its factors. -/
@[stacks 016R "universal property of binary products as a Hom equivalence",
  stacks 0170 "universal property of binary products as a Hom equivalence"]
noncomputable def homEquiv (W : C) :
    (W ⟶ X ⨯ Y) ≃ (W ⟶ X) × (W ⟶ Y) :=
  (Pi.homEquiv (pairFunction X Y) W).trans
    (WalkingPair.piEquiv (fun j ↦ W ⟶ pairFunction X Y j))

namespace homEquiv

/-- The value of `prod.homEquiv` is the pair of projection composites. -/
@[simp, stacks 016R "binary-product Hom equivalence application",
  stacks 0170 "binary-product Hom equivalence application"]
theorem apply {W : C} (h : W ⟶ X ⨯ Y) :
    homEquiv X Y W h = (h ≫ prod.fst, h ≫ prod.snd) := sorry

/-- The first component returned by `prod.homEquiv`. -/
@[simp, stacks 016R "first component of the binary-product Hom equivalence",
  stacks 0170 "first component of the binary-product Hom equivalence"]
theorem apply_fst {W : C} (h : W ⟶ X ⨯ Y) :
    (homEquiv X Y W h).1 = h ≫ prod.fst := sorry

/-- The second component returned by `prod.homEquiv`. -/
@[simp, stacks 016R "second component of the binary-product Hom equivalence",
  stacks 0170 "second component of the binary-product Hom equivalence"]
theorem apply_snd {W : C} (h : W ⟶ X ⨯ Y) :
    (homEquiv X Y W h).2 = h ≫ prod.snd := sorry

/-- The inverse of `prod.homEquiv` is the canonical binary-product lift. -/
@[simp, stacks 016R "inverse of the binary-product Hom equivalence",
  stacks 0170 "inverse of the binary-product Hom equivalence"]
theorem symm_apply {W : C} (p : (W ⟶ X) × (W ⟶ Y)) :
    (homEquiv X Y W).symm p = prod.lift p.1 p.2 := sorry

/-- The binary-product Hom equivalence is natural under precomposition. -/
@[simp, stacks 016R "naturality of the binary-product Hom equivalence",
  stacks 0170 "naturality of the binary-product Hom equivalence"]
theorem precomp {V W : C} (k : V ⟶ W) (h : W ⟶ X ⨯ Y) :
    homEquiv X Y V (k ≫ h) =
      (k ≫ (homEquiv X Y W h).1, k ≫ (homEquiv X Y W h).2) := sorry

/-- The inverse binary-product Hom equivalence commutes with precomposition. -/
@[stacks 016R "inverse naturality of the binary-product Hom equivalence",
  stacks 0170 "inverse naturality of the binary-product Hom equivalence"]
theorem symm_precomp {V W : C} (k : V ⟶ W) (p : (W ⟶ X) × (W ⟶ Y)) :
    (homEquiv X Y V).symm (k ≫ p.1, k ≫ p.2) =
      k ≫ (homEquiv X Y W).symm p := sorry

end homEquiv

end prod

namespace coprod

variable {C : Type u} [Category.{v} C]
variable (X Y : C) [HasBinaryCoproduct X Y]

/-- Morphisms from a binary coproduct are equivalent to pairs of morphisms from its factors. -/
@[stacks 04AN "universal property of binary coproducts as a Hom equivalence"]
noncomputable def homEquiv (W : C) :
    (X ⨿ Y ⟶ W) ≃ (X ⟶ W) × (Y ⟶ W) :=
  (Sigma.homEquiv (pairFunction X Y) W).trans
    (WalkingPair.piEquiv (fun j ↦ pairFunction X Y j ⟶ W))

namespace homEquiv

/-- The value of `coprod.homEquiv` is the pair of inclusion composites. -/
@[simp, stacks 04AN "binary-coproduct Hom equivalence application"]
theorem apply {W : C} (h : X ⨿ Y ⟶ W) :
    homEquiv X Y W h = (coprod.inl ≫ h, coprod.inr ≫ h) := sorry

/-- The first component returned by `coprod.homEquiv`. -/
@[simp, stacks 04AN "first component of the binary-coproduct Hom equivalence"]
theorem apply_inl {W : C} (h : X ⨿ Y ⟶ W) :
    (homEquiv X Y W h).1 = coprod.inl ≫ h := sorry

/-- The second component returned by `coprod.homEquiv`. -/
@[simp, stacks 04AN "second component of the binary-coproduct Hom equivalence"]
theorem apply_inr {W : C} (h : X ⨿ Y ⟶ W) :
    (homEquiv X Y W h).2 = coprod.inr ≫ h := sorry

/-- The inverse of `coprod.homEquiv` is the canonical binary-coproduct descent. -/
@[simp, stacks 04AN "inverse of the binary-coproduct Hom equivalence"]
theorem symm_apply {W : C} (p : (X ⟶ W) × (Y ⟶ W)) :
    (homEquiv X Y W).symm p = coprod.desc p.1 p.2 := sorry

/-- The binary-coproduct Hom equivalence is natural under postcomposition. -/
@[simp, stacks 04AN "naturality of the binary-coproduct Hom equivalence"]
theorem postcomp {V W : C} (h : X ⨿ Y ⟶ V) (k : V ⟶ W) :
    homEquiv X Y W (h ≫ k) =
      ((homEquiv X Y V h).1 ≫ k, (homEquiv X Y V h).2 ≫ k) := sorry

/-- The inverse binary-coproduct Hom equivalence commutes with postcomposition. -/
@[stacks 04AN "inverse naturality of the binary-coproduct Hom equivalence"]
theorem symm_postcomp {V W : C} (p : (X ⟶ V) × (Y ⟶ V)) (k : V ⟶ W) :
    (homEquiv X Y W).symm (p.1 ≫ k, p.2 ≫ k) =
      (homEquiv X Y V).symm p ≫ k := sorry

end homEquiv

end coprod

end CategoryTheory.Limits
