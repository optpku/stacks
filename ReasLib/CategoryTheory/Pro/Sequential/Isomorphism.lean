module

public import ReasLib.CategoryTheory.Pro.Sequential.Shift
public import ReasLib.CategoryTheory.Pro.Sequential.CommonRefinement.Functoriality
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Isomorphisms of sequential pro-morphism representatives

The categorical notion of invertibility belongs to `IsIso r.toHom`.  A sequential presentation
also has a useful concrete inverse criterion, stated here in terms of another monotone
representative and common refinements.
-/

@[expose] public section

open CategoryTheory Opposite

universe u v uD vD

namespace CategoryTheory

namespace Pro.SequentialHom

variable {C : Type u} [Category.{v} C]
variable {X Y : SequentialInverseSystem C}

/-- A natural transformation `α : X ⟶ Y` and a map `Y.shift c ⟶ X` are inverse up to the
transition maps across the fixed shift `c`.

This is the constant-shift criterion commonly used to identify two sequential presentations of
the same pro-object. -/
@[stacks 0G3K "constant-shift inverse for sequential pro-objects"]
def IsShiftInverse (α : X ⟶ Y) (c : ℕ) (β : Y.shift c ⟶ X) : Prop :=
  (∀ n : ℕ,
      α.app (op (c + n)) ≫ β.app (op n) =
        X.transitionMap (Nat.le_add_left n c)) ∧
    ∀ n : ℕ,
      β.app (op n) ≫ α.app (op n) =
        Y.transitionMap (Nat.le_add_left n c)

/-- A sequential representative has a representative inverse when it admits an inverse up to the
common-refinement relation. -/
@[stacks 0G3C]
def HasRepresentativeInverse (r : Pro.SequentialHom X Y) : Prop :=
  ∃ s : Pro.SequentialHom Y X,
    Equivalent (comp r s) (id X) ∧ Equivalent (comp s r) (id Y)

namespace IsShiftInverse

/-- Stagewise functors preserve a constant-shift inverse. -/
@[stacks 0G3K "stagewise functor preserves a shifted inverse"]
theorem whiskerRight {D : Type uD} [Category.{vD} D]
    {α : X ⟶ Y} {c : ℕ} {β : Y.shift c ⟶ X}
    (h : IsShiftInverse α c β) (F : C ⥤ D) :
    IsShiftInverse (Functor.whiskerRight α F) c (Functor.whiskerRight β F) := sorry

/-- The forward map at the shifted index followed by its shift inverse is the source transition. -/
theorem forward_comp
    {α : X ⟶ Y} {c : ℕ} {β : Y.shift c ⟶ X}
    (h : IsShiftInverse α c β) (n : ℕ) :
    α.app (op (c + n)) ≫ β.app (op n) =
      X.transitionMap (Nat.le_add_left n c) := sorry

/-- The shift inverse followed by the forward map is the target transition. -/
theorem reverse_comp
    {α : X ⟶ Y} {c : ℕ} {β : Y.shift c ⟶ X}
    (h : IsShiftInverse α c β) (n : ℕ) :
    β.app (op n) ≫ α.app (op n) =
      Y.transitionMap (Nat.le_add_left n c) := sorry

/-- A constant-shift inverse gives a representative inverse for the natural-transformation
presentation. -/
theorem hasRepresentativeInverse
    {α : X ⟶ Y} {c : ℕ} {β : Y.shift c ⟶ X}
    (h : IsShiftInverse α c β) :
    (ofNatTrans α).HasRepresentativeInverse := sorry

/-- A natural transformation admitting an inverse after a fixed shift induces an isomorphism of
the associated pro-objects. -/
@[stacks 0G3K "constant-shift criterion for pro-isomorphisms"]
theorem isIso
    {α : X ⟶ Y} {c : ℕ} {β : Y.shift c ⟶ X}
    (h : IsShiftInverse α c β) :
    IsIso (ofNatTrans α).toHom := sorry

/-- The shifted reverse representative in constant-shift inverse data is also an isomorphism of
the associated pro-objects. -/
@[stacks 0G3K "reverse constant-shift criterion for pro-isomorphisms"]
theorem reverse_isIso
    {α : X ⟶ Y} {c : ℕ} {β : Y.shift c ⟶ X}
    (h : IsShiftInverse α c β) :
    IsIso (ofShiftNatTrans c β).toHom := sorry

end IsShiftInverse

/-- The arithmetic transition index for two shifted maps. -/
@[stacks 0G3K "two-sided shift transition index"]
theorem shift_le (c d n : ℕ) : n ≤ c + (d + n) := sorry

/-- Inverse data for a pair of natural transformations with shifts on both sides. -/
@[stacks 0G3K "two-sided shifted inverse for sequential pro-objects"]
def IsShiftedInverse
    {X Y : SequentialInverseSystem C} (c d : ℕ)
    (α : X.shift c ⟶ Y) (β : Y.shift d ⟶ X) : Prop :=
  (∀ n : ℕ,
      α.app (op (d + n)) ≫ β.app (op n) =
        X.transitionMap (shift_le c d n)) ∧
    ∀ n : ℕ,
      β.app (op (c + n)) ≫ α.app (op n) =
        Y.transitionMap (shift_le d c n)

namespace IsShiftedInverse

/-- The first shifted composite is the source transition. -/
theorem forward_comp
    {X Y : SequentialInverseSystem C} {c d : ℕ}
    {α : X.shift c ⟶ Y} {β : Y.shift d ⟶ X}
    (h : IsShiftedInverse c d α β) (n : ℕ) :
    α.app (op (d + n)) ≫ β.app (op n) =
      X.transitionMap (shift_le c d n) := sorry

/-- The second shifted composite is the target transition. -/
theorem reverse_comp
    {X Y : SequentialInverseSystem C} {c d : ℕ}
    {α : X.shift c ⟶ Y} {β : Y.shift d ⟶ X}
    (h : IsShiftedInverse c d α β) (n : ℕ) :
    β.app (op (c + n)) ≫ α.app (op n) =
      Y.transitionMap (shift_le d c n) := sorry

/-- Two-sided shifted inverse data gives a representative inverse. -/
theorem hasRepresentativeInverse
    {X Y : SequentialInverseSystem C} {c d : ℕ}
    {α : X.shift c ⟶ Y} {β : Y.shift d ⟶ X}
    (h : IsShiftedInverse c d α β) :
    (ofShiftNatTrans c α).HasRepresentativeInverse := sorry

/-- Two-sided shifted inverse data gives an isomorphism of the associated pro-objects. -/
@[stacks 0G3K "two-sided shifted pro-isomorphism criterion"]
theorem isIso
    {X Y : SequentialInverseSystem C} {c d : ℕ}
    {α : X.shift c ⟶ Y} {β : Y.shift d ⟶ X}
    (h : IsShiftedInverse c d α β) :
    IsIso (ofShiftNatTrans c α).toHom := sorry

/-- The explicit isomorphism of pro-objects determined by two-sided shifted inverse data. -/
@[stacks 0G3K "explicit two-sided shifted pro-isomorphism"]
noncomputable def iso
    {X Y : SequentialInverseSystem C} {c d : ℕ}
    {α : X.shift c ⟶ Y} {β : Y.shift d ⟶ X}
    (h : IsShiftedInverse c d α β) :
    (Pro.lim (C := C) ℕᵒᵖ).obj X ≅ (Pro.lim (C := C) ℕᵒᵖ).obj Y where
  hom := (ofShiftNatTrans c α).toHom
  inv := (ofShiftNatTrans d β).toHom
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of the explicit shifted pro-isomorphism is the original representative. -/
@[simp, stacks 0G3K "explicit shifted pro-isomorphism forward map"]
theorem iso_hom
    {X Y : SequentialInverseSystem C} {c d : ℕ}
    {α : X.shift c ⟶ Y} {β : Y.shift d ⟶ X}
    (h : IsShiftedInverse c d α β) :
    h.iso.hom = (ofShiftNatTrans c α).toHom := sorry

/-- The inverse map of the explicit shifted pro-isomorphism is the reverse representative. -/
@[simp, stacks 0G3K "explicit shifted pro-isomorphism inverse map"]
theorem iso_inv
    {X Y : SequentialInverseSystem C} {c d : ℕ}
    {α : X.shift c ⟶ Y} {β : Y.shift d ⟶ X}
    (h : IsShiftedInverse c d α β) :
    h.iso.inv = (ofShiftNatTrans d β).toHom := sorry

end IsShiftedInverse

/-- A representative inverse induces an isomorphism of the associated
pro-objects. -/
theorem isIso_toHom_of_hasRepresentativeInverse (r : Pro.SequentialHom X Y)
    (h : r.HasRepresentativeInverse) :
    IsIso r.toHom := sorry

/-- Every isomorphism of the pro-morphisms represented by `r` admits a representative-level
inverse after monotone refinement. -/
theorem hasRepresentativeInverse_of_isIso_toHom (r : Pro.SequentialHom X Y)
    (h : IsIso r.toHom) :
    r.HasRepresentativeInverse := sorry

/-- A sequential representative has a representative inverse exactly when its associated
pro-morphism is categorically invertible. -/
theorem isIso_toHom_iff_hasRepresentativeInverse (r : Pro.SequentialHom X Y) :
    IsIso r.toHom ↔ r.HasRepresentativeInverse := sorry

/-- Applying a functor stagewise preserves the invertibility of the pro-morphism represented by
a sequential representative. -/
theorem isIso_toHom_map {D : Type uD} [Category.{vD} D]
    (r : Pro.SequentialHom X Y) (h : IsIso r.toHom) (F : C ⥤ D) :
    IsIso (r.map F).toHom := sorry

/-- Whiskering a natural transformation of sequential inverse systems on the right preserves the
invertibility of the induced pro-morphism. -/
theorem isIso_toHom_whiskerRight {D : Type uD} [Category.{vD} D]
    (α : X ⟶ Y) (h : IsIso (ofNatTrans α).toHom) (F : C ⥤ D) :
    IsIso (ofNatTrans (Functor.whiskerRight α F)).toHom := sorry

namespace HasRepresentativeInverse

/-- Functorial postcomposition carries a representative inverse to a representative inverse. -/
theorem map {D : Type uD} [Category.{vD} D] {r : Pro.SequentialHom X Y}
    (h : r.HasRepresentativeInverse) (F : C ⥤ D) :
    (r.map F).HasRepresentativeInverse := sorry

/-- Under a natural transformation with a representative inverse, every target transition map
eventually factors through the corresponding component of that transformation. -/
theorem targetTransition_factors (α : X ⟶ Y)
    (h : (ofNatTrans α).HasRepresentativeInverse) (n : ℕ) :
    ∃ (m : ℕ) (hnm : n ≤ m) (t : Y.obj (op m) ⟶ X.obj (op n)),
      Y.transitionMap hnm = t ≫ α.app (op n) := sorry

/-- Under a natural transformation with a representative inverse, every source transition map
eventually factors through a later component of that transformation. -/
theorem sourceTransition_factors (α : X ⟶ Y)
    (h : (ofNatTrans α).HasRepresentativeInverse) (n : ℕ) :
    ∃ (m : ℕ) (hnm : n ≤ m) (t : Y.obj (op m) ⟶ X.obj (op n)),
      X.transitionMap hnm = α.app (op m) ≫ t := sorry

end HasRepresentativeInverse

end Pro.SequentialHom

end CategoryTheory
