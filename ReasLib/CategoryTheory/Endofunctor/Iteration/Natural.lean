module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.EqToHom
public import Mathlib.CategoryTheory.Functor.Currying
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Natural-number endofunctor iteration

This leaf owns zero-based endofunctor iterates, folds and unfolds, functorial maps between
iterates, and coherent additive factorizations. Positive iterates and their inserted structure
maps live in focused downstream leaves.
-/

@[expose] public section

open CategoryTheory

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace Endofunctor

/-- The zero-based iterate of an endofunctor.  The zeroth iterate is the identity functor and each
successor is obtained by composing one more copy on the right. -/
@[stacks 0G5M "zero-based endofunctor iteration"]
def iterate (Y : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => iterate Y n ⋙ Y

/-- The zeroth endofunctor iterate is the identity functor. -/
@[simp, stacks 0G5M "zero iterate computation"]
theorem iterate.zero (Y : C ⥤ C) : iterate Y 0 = 𝟭 C := by
  rfl

/-- A successor iterate is obtained by right composition with the endofunctor. -/
@[simp, stacks 0G5M "successor iterate computation"]
theorem iterate.succ (Y : C ⥤ C) (n : ℕ) : iterate Y (n + 1) = iterate Y n ⋙ Y := by
  rfl

/-- The first endofunctor iterate is canonically isomorphic to the endofunctor. -/
@[stacks 0G5M "first endofunctor iterate"]
def iterate.oneIso (Y : C ⥤ C) : iterate Y 1 ≅ Y := Functor.leftUnitor Y

/-- Endofunctor iteration agrees with iteration of right-composition as an ordinary function. -/
@[stacks 0G5M "endofunctor iteration as function iteration"]
theorem iterate.eq_natIterate (Y : C ⥤ C) (n : ℕ) :
    iterate Y n = Nat.iterate (fun F : C ⥤ C ↦ F ⋙ Y) n (𝟭 C) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate.succ, Function.iterate_succ_apply', ih]

/-- Evaluating an endofunctor iterate agrees with iterating its object function. -/
@[simp, stacks 0G5M "object formula for an endofunctor iterate"]
theorem iterate.obj (Y : C ⥤ C) (n : ℕ) (X : C) :
    (iterate Y n).obj X = Nat.iterate Y.obj n X := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate.succ, Function.iterate_succ_apply', Functor.comp_obj, ih]

/-- Fold an algebra map `a : Y(A) ⟶ A` across a zero-based iterate of the endofunctor.  The
resulting map has source `(iterate Y n).obj A` and target `A`. -/
@[stacks 0G5M "iterated endofunctor algebra map"]
def iterate.fold (Y : C ⥤ C) {A : C} (a : Y.obj A ⟶ A) :
    (n : ℕ) → (iterate Y n).obj A ⟶ A
  | 0 => 𝟙 A
  | n + 1 => Y.map (iterate.fold Y a n) ≫ a

/-- Folding at the zeroth iterate is the identity. -/
@[simp, stacks 0G5M "zero iterated algebra map"]
theorem iterate.fold_zero (Y : C ⥤ C) {A : C} (a : Y.obj A ⟶ A) :
    iterate.fold Y a 0 = 𝟙 A := by
  rfl

/-- Folding at a successor first applies the functor to the preceding fold and then the algebra
map. -/
@[simp, stacks 0G5M "successor iterated algebra map"]
theorem iterate.fold_succ (Y : C ⥤ C) {A : C} (a : Y.obj A ⟶ A) (n : ℕ) :
    iterate.fold Y a (n + 1) = Y.map (iterate.fold Y a n) ≫ a := by
  rfl

/-- An algebra morphism commutes with every iterated fold. -/
@[stacks 0G5M "naturality of iterated endofunctor algebra maps"]
theorem iterate.fold_naturality
    (Y : C ⥤ C) {A B : C} (a : Y.obj A ⟶ A) (b : Y.obj B ⟶ B)
    (f : A ⟶ B) (hf : Y.map f ≫ b = a ≫ f) (n : ℕ) :
    (iterate Y n).map f ≫ iterate.fold Y b n = iterate.fold Y a n ≫ f := by
  induction n with
  | zero =>
      change f ≫ 𝟙 B = 𝟙 A ≫ f
      simp
  | succ n ih =>
      change Y.map ((iterate Y n).map f) ≫ (Y.map (iterate.fold Y b n) ≫ b) =
        (Y.map (iterate.fold Y a n) ≫ a) ≫ f
      rw [← Category.assoc, ← Y.map_comp, ih, Y.map_comp, Category.assoc, hf]
      simp only [Category.assoc]

/-- Unfold a coalgebra map `c : A ⟶ Y(A)` across a zero-based iterate of the endofunctor.  The
resulting map has source `A` and target `(iterate Y n).obj A`. -/
@[stacks 0G5M "iterated endofunctor coalgebra map"]
def iterate.unfold (Y : C ⥤ C) {A : C} (c : A ⟶ Y.obj A) :
    (n : ℕ) → A ⟶ (iterate Y n).obj A
  | 0 => 𝟙 A
  | n + 1 => c ≫ Y.map (iterate.unfold Y c n)

/-- Unfolding at the zeroth iterate is the identity. -/
@[simp, stacks 0G5M "zero iterated coalgebra map"]
theorem iterate.unfold_zero (Y : C ⥤ C) {A : C} (c : A ⟶ Y.obj A) :
    iterate.unfold Y c 0 = 𝟙 A := by
  rfl

/-- Unfolding at a successor first applies the coalgebra map and then maps the preceding unfold
through the endofunctor. -/
@[simp, stacks 0G5M "successor iterated coalgebra map"]
theorem iterate.unfold_succ (Y : C ⥤ C) {A : C} (c : A ⟶ Y.obj A) (n : ℕ) :
    iterate.unfold Y c (n + 1) = c ≫ Y.map (iterate.unfold Y c n) := by
  rfl

/-- A coalgebra morphism commutes with every iterated unfold. -/
@[stacks 0G5M "naturality of iterated endofunctor coalgebra maps"]
theorem iterate.unfold_naturality
    (Y : C ⥤ C) {A B : C} (a : A ⟶ Y.obj A) (b : B ⟶ Y.obj B)
    (f : A ⟶ B) (hf : f ≫ b = a ≫ Y.map f) (n : ℕ) :
    f ≫ iterate.unfold Y b n = iterate.unfold Y a n ≫ (iterate Y n).map f := by
  induction n with
  | zero =>
      change f ≫ 𝟙 B = 𝟙 A ≫ f
      simp
  | succ n ih =>
      change f ≫ (b ≫ Y.map (iterate.unfold Y b n)) =
        (a ≫ Y.map (iterate.unfold Y a n)) ≫ Y.map ((iterate Y n).map f)
      rw [← Category.assoc, hf, Category.assoc, ← Y.map_comp, ih]
      simp only [Y.map_comp, Category.assoc]

/-- Apply a natural transformation in every factor of a zero-based endofunctor iterate. -/
@[stacks 0G5N "map between zero-based endofunctor iterates"]
def iterate.map {Y Z : C ⥤ C} (α : Y ⟶ Z) : (n : ℕ) → iterate Y n ⟶ iterate Z n
  | 0 => 𝟙 (𝟭 C)
  | n + 1 => iterate.map α n ◫ α

/-- In degree zero, a map between endofunctor iterates is the identity of the identity functor. -/
@[simp, stacks 0G5M "zero map between endofunctor iterates"]
theorem iterate.map.zero {Y Z : C ⥤ C} (α : Y ⟶ Z) :
    iterate.map α 0 = 𝟙 (𝟭 C) := by
  rfl

/-- At a successor, maps between iterates compose horizontally. -/
@[simp, stacks 0G5M "successor map between endofunctor iterates"]
theorem iterate.map.succ {Y Z : C ⥤ C} (α : Y ⟶ Z) (n : ℕ) :
    iterate.map α (n + 1) = iterate.map α n ◫ α := by
  rfl

/-- The component of a successor iterated map is the horizontal-composition component. -/
@[simp, stacks 0G5M "component of a successor iterate map"]
theorem iterate.map.succ_app {Y Z : C ⥤ C} (α : Y ⟶ Z) (n : ℕ) (X : C) :
    (iterate.map α (n + 1)).app X =
      α.app ((iterate Y n).obj X) ≫ Z.map ((iterate.map α n).app X) := by
  rfl

/-- Iterating an identity natural transformation gives the identity at every degree. -/
@[simp, stacks 0G5M "identity map between endofunctor iterates"]
theorem iterate.map.id (Y : C ⥤ C) (n : ℕ) :
    iterate.map (𝟙 Y) n = 𝟙 (iterate Y n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iterate.map.succ, ih]
      cat_disch

/-- Iterated maps preserve composition of natural transformations. -/
@[simp, stacks 0G5M "composition of maps between endofunctor iterates"]
theorem iterate.map.comp {Y Z W : C ⥤ C} (α : Y ⟶ Z) (β : Z ⟶ W) (n : ℕ) :
    iterate.map (α ≫ β) n = iterate.map α n ≫ iterate.map β n := by
  induction n with
  | zero =>
      change 𝟙 (𝟭 C) = (𝟙 (𝟭 C) : 𝟭 C ⟶ 𝟭 C) ≫ 𝟙 (𝟭 C)
      rw [Category.comp_id]
  | succ n ih =>
      rw [iterate.map.succ, iterate.map.succ, iterate.map.succ, ih, NatTrans.exchange]
      rfl

/-- Taking the `n`-th iterate is a functor on the category of endofunctors. -/
@[stacks 0G5N "fixed endofunctor iterate functor"]
def iterate.functor (n : ℕ) : (C ⥤ C) ⥤ (C ⥤ C) where
  obj Y := iterate Y n
  map α := iterate.map α n
  map_id Y := iterate.map.id Y n
  map_comp α β := iterate.map.comp α β n

/-- The comparison from the first iterate to the original endofunctor is natural in the
endofunctor. -/
@[stacks 0G5N "naturality of the first endofunctor iterate"]
theorem iterate.oneIso.hom.naturality {Y Z : C ⥤ C} (α : Y ⟶ Z) :
    iterate.map α 1 ≫ (iterate.oneIso Z).hom = (iterate.oneIso Y).hom ≫ α := by
  ext X
  change (α.app X ≫ Z.map (𝟙 X)) ≫ 𝟙 (Z.obj X) = 𝟙 (Y.obj X) ≫ α.app X
  simp

/-- The inverse of the first-iterate comparison is natural in the endofunctor. -/
@[stacks 0G5N "inverse naturality of the first endofunctor iterate"]
theorem iterate.oneIso.inv.naturality {Y Z : C ⥤ C} (α : Y ⟶ Z) :
    α ≫ (iterate.oneIso Z).inv = (iterate.oneIso Y).inv ≫ iterate.map α 1 := by
  apply (cancel_mono (iterate.oneIso Z).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    iterate.oneIso.hom.naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Taking the first iterate is naturally isomorphic to the identity on endofunctors. -/
@[stacks 0G5N "first endofunctor iterate natural isomorphism"]
def iterate.oneNatIso : iterate.functor (C := C) 1 ≅ 𝟭 (C ⥤ C) :=
  NatIso.ofComponents (fun Y ↦ iterate.oneIso Y)
    (fun α ↦ iterate.oneIso.hom.naturality α)

/-- The component of the first-iterate natural isomorphism is the canonical left unitor. -/
@[simp, stacks 0G5M "component of the first-iterate natural isomorphism"]
theorem iterate.oneNatIso.app (Y : C ⥤ C) :
    iterate.oneNatIso.app Y = iterate.oneIso Y := by
  rfl

/-- The functor sending an endofunctor `Y` to the composite of its `n`-th and `m`-th
zero-based iterates. -/
@[stacks 0G5N "composite of fixed endofunctor iterates"]
def iterate.compositeFunctor (n m : ℕ) : (C ⥤ C) ⥤ (C ⥤ C) :=
  (iterate.functor m).prod' (iterate.functor n) ⋙
    Functor.uncurry.obj (Functor.whiskeringRight C C C)

/-- The composite-iterate functor evaluates to composition of the two selected iterates. -/
@[simp, stacks 0G5M "object formula for composite iterates"]
theorem iterate.compositeFunctor.obj (n m : ℕ) (Y : C ⥤ C) :
    (iterate.compositeFunctor n m).obj Y = iterate Y n ⋙ iterate Y m := by
  rfl

/-- The composite-iterate functor maps a natural transformation by horizontal composition. -/
@[simp, stacks 0G5M "map formula for composite iterates"]
theorem iterate.compositeFunctor.map {Y Z : C ⥤ C} (α : Y ⟶ Z) (n m : ℕ) :
    (iterate.compositeFunctor n m).map α = iterate.map α n ◫ iterate.map α m := by
  rfl

/-- The canonical factorization of an endofunctor iterate into two consecutive iterates. -/
@[stacks 0G5M "endofunctor iterate factorization"]
def iterate.addIso (Y : C ⥤ C) (n : ℕ) :
    (m : ℕ) → iterate Y (n + m) ≅ iterate Y n ⋙ iterate Y m
  | 0 => (Functor.rightUnitor (iterate Y n)).symm
  | m + 1 =>
      Functor.isoWhiskerRight (iterate.addIso Y n m) Y ≪≫
        Functor.associator (iterate Y n) (iterate Y m) Y

/-- The zero-right-factor case of iterate factorization is the right unitor. -/
@[simp, stacks 0G5M "zero-right-factor iterate factorization"]
theorem iterate.addIso.zero (Y : C ⥤ C) (n : ℕ) :
    iterate.addIso Y n 0 = (Functor.rightUnitor (iterate Y n)).symm := by
  rfl

/-- The successor case of iterate factorization is obtained recursively using the associator. -/
@[simp, stacks 0G5M "successor iterate factorization"]
theorem iterate.addIso.succ (Y : C ⥤ C) (n m : ℕ) :
    iterate.addIso Y n (m + 1) =
      Functor.isoWhiskerRight (iterate.addIso Y n m) Y ≪≫
        Functor.associator (iterate Y n) (iterate Y m) Y := by
  rfl

/-- Transport an endofunctor iterate along an equality of its indices. -/
@[stacks 0G5M "index transport for endofunctor iterates"]
def iterate.indexIso (Y : C ⥤ C) {n m : ℕ} (h : n = m) : iterate Y n ≅ iterate Y m :=
  eqToIso (congrArg (iterate Y) h)

set_option backward.isDefEq.respectTransparency false in
/-- Splitting off a zeroth left iterate is the inverse left unitor, after canonical index
transport. -/
@[simp, stacks 0G5M "zero-left-factor iterate factorization"]
theorem iterate.addIso.zero_left (Y : C ⥤ C) (n : ℕ) :
    iterate.addIso Y 0 n =
      iterate.indexIso Y (Nat.zero_add n) ≪≫
        (Functor.leftUnitor (iterate Y n)).symm := by
  induction n with
  | zero =>
      dsimp [iterate.addIso, iterate.indexIso]
      cat_disch
  | succ n ih =>
      rw [iterate.addIso.succ, ih]
      ext X
      simp [iterate.indexIso, iterate, eqToHom_map]
      exact Category.comp_id _

set_option backward.isDefEq.respectTransparency false in
/-- Factoring an iterate into three consecutive blocks is associative. -/
@[stacks 0G5M "associativity of endofunctor iterate factorization"]
theorem iterate.addIso.assoc (Y : C ⥤ C) (n m k : ℕ) :
    iterate.addIso Y (n + m) k ≪≫
        Functor.isoWhiskerRight (iterate.addIso Y n m) (iterate Y k) ≪≫
        Functor.associator (iterate Y n) (iterate Y m) (iterate Y k) =
      iterate.indexIso Y (Nat.add_assoc n m k) ≪≫ iterate.addIso Y n (m + k) ≪≫
        Functor.isoWhiskerLeft (iterate Y n) (iterate.addIso Y m k) := by
  induction k with
  | zero =>
      ext X
      simp [iterate.addIso, iterate.indexIso, iterate]
      exact (Category.comp_id _).symm
  | succ k ih =>
      ext X
      have ihX := congrArg (fun e => e.hom.app X) ih
      simp [iterate.indexIso] at ihX
      simp [iterate.addIso, iterate.indexIso, iterate]
      have h := congrArg (fun f => Y.map f) ihX
      simp only [Y.map_comp, eqToHom_map] at h
      rw [← Category.comp_id
        (Y.map ((iterate.addIso Y m k).hom.app ((iterate Y n).obj X)))] at h
      exact h

set_option backward.isDefEq.respectTransparency false in
/-- Iterate factorization is natural in the endofunctor. -/
@[stacks 0G5N "naturality of endofunctor iterate factorization"]
theorem iterate.addIso.hom.naturality {Y Z : C ⥤ C} (α : Y ⟶ Z) (n m : ℕ) :
    iterate.map α (n + m) ≫ (iterate.addIso Z n m).hom =
      (iterate.addIso Y n m).hom ≫ (iterate.map α n ◫ iterate.map α m) := by
  induction m with
  | zero =>
      ext X
      simp [iterate.addIso, iterate.map, iterate]
  | succ m ih =>
      ext X
      simp [iterate.addIso, iterate.map, iterate, Category.assoc]
      have ihX := NatTrans.congr_app ih X
      dsimp only [NatTrans.comp_app, NatTrans.hcomp] at ihX
      rw [← Z.map_comp, ihX]
      rw [Z.map_comp, Z.map_comp, ← Category.assoc, ← α.naturality]
      simp only [Category.assoc]
      rfl

/-- The inverse iterate factorization is natural in the endofunctor. -/
@[stacks 0G5N "inverse naturality of endofunctor iterate factorization"]
theorem iterate.addIso.inv.naturality {Y Z : C ⥤ C} (α : Y ⟶ Z) (n m : ℕ) :
    (iterate.map α n ◫ iterate.map α m) ≫ (iterate.addIso Z n m).inv =
      (iterate.addIso Y n m).inv ≫ iterate.map α (n + m) := by
  apply (cancel_mono (iterate.addIso Z n m).hom).1
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    iterate.addIso.hom.naturality, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Splitting an iterate at `n + m` is a natural isomorphism in the endofunctor being iterated. -/
@[stacks 0G5N "natural endofunctor iterate factorization"]
def iterate.addNatIso (n m : ℕ) :
    iterate.functor (C := C) (n + m) ≅ iterate.compositeFunctor (C := C) n m :=
  NatIso.ofComponents (fun Y ↦ iterate.addIso Y n m)
    (fun α ↦ iterate.addIso.hom.naturality α n m)

/-- The component of the natural iterate factorization is the canonical pointwise
factorization. -/
@[simp, stacks 0G5M "component of the natural iterate factorization"]
theorem iterate.addNatIso.app (n m : ℕ) (Y : C ⥤ C) :
    (iterate.addNatIso n m).app Y = iterate.addIso Y n m := by
  rfl

end Endofunctor



end CategoryTheory
