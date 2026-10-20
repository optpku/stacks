module

public import Mathlib.CategoryTheory.Functor.Category
public import Mathlib.CategoryTheory.Types.Basic

/-!
# Groupoids in functors

A groupoid in functors on a category `C` is a quintuple of object and arrow functors,
source, target, and pointwise composition, such that the evaluation at every object of
`C` is a groupoid category.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory

/-- A quintuple `(U, R, src, tgt, comp)` of functors `C ⥤ Type v` is a groupoid in functors
on `C` when source and target of composition, associativity, identities, inverses, and
naturality of composition hold pointwise. -/
class IsGroupoidInFunctors {C : Type u} [Category.{v} C]
    (U R : C ⥤ Type v) (src tgt : R ⟶ U)
    (comp : {T : C} → (a b : R.obj T) → src.app T a = tgt.app T b → R.obj T) : Prop where
  /-- The source of a composite is the source of the earlier arrow. -/
  comp_src : ∀ {T : C} (a b : R.obj T) (h : src.app T a = tgt.app T b),
    src.app T (comp a b h) = src.app T b
  /-- The target of a composite is the target of the later arrow. -/
  comp_tgt : ∀ {T : C} (a b : R.obj T) (h : src.app T a = tgt.app T b),
    tgt.app T (comp a b h) = tgt.app T a
  /-- Composition of composable arrows is associative. -/
  assoc : ∀ {T : C} (a b d : R.obj T)
      (h_ab : src.app T a = tgt.app T b) (h_bd : src.app T b = tgt.app T d)
      (h_ab_d : src.app T (comp a b h_ab) = tgt.app T d)
      (h_a_bd : src.app T a = tgt.app T (comp b d h_bd)),
    comp (comp a b h_ab) d h_ab_d = comp a (comp b d h_bd) h_a_bd
  /-- Every object has an identity arrow which is a two-sided unit. -/
  exists_id : ∀ {T : C} (x : U.obj T),
    ∃ (e : R.obj T), src.app T e = x ∧ tgt.app T e = x ∧
      (∀ (a : R.obj T) (h : src.app T a = tgt.app T e), comp a e h = a) ∧
        (∀ (a : R.obj T) (h : src.app T e = tgt.app T a), comp e a h = a)
  /-- Every arrow has an inverse whose composites are identities. -/
  exists_inv : ∀ {T : C} (a : R.obj T),
    ∃ (i : R.obj T) (h_ai : src.app T a = tgt.app T i)
      (h_ia : src.app T i = tgt.app T a),
      (∀ (b : R.obj T) (h : src.app T b = tgt.app T (comp a i h_ai)),
          comp b (comp a i h_ai) h = b) ∧
        (∀ (b : R.obj T) (h : src.app T (comp a i h_ai) = tgt.app T b),
          comp (comp a i h_ai) b h = b) ∧
        (∀ (b : R.obj T) (h : src.app T b = tgt.app T (comp i a h_ia)),
          comp b (comp i a h_ia) h = b) ∧
        (∀ (b : R.obj T) (h : src.app T (comp i a h_ia) = tgt.app T b),
          comp (comp i a h_ia) b h = b)
  /-- Composition is natural in the test object. -/
  naturality : ∀ {T T' : C} (f : T ⟶ T') (a b : R.obj T)
      (h : src.app T a = tgt.app T b)
      (h' : src.app T' (R.map f a) = tgt.app T' (R.map f b)),
    R.map f (comp a b h) = comp (R.map f a) (R.map f b) h'

/-- The discrete groupoid in functors on a single functor, with identity source and target. -/
instance instIsGroupoidInFunctorsId {C : Type u} [Category.{v} C] (U : C ⥤ Type v) :
    IsGroupoidInFunctors U U (𝟙 U) (𝟙 U) (fun {_} a b _ ↦ a) :=
  sorry

/-- A quintuple is a groupoid in functors precisely when the pointwise groupoid laws hold. -/
theorem isGroupoidInFunctors_iff {C : Type u} [Category.{v} C]
    (U R : C ⥤ Type v) (src tgt : R ⟶ U)
    (comp : {T : C} → (a b : R.obj T) → src.app T a = tgt.app T b → R.obj T) :
    IsGroupoidInFunctors U R src tgt comp ↔
      (∀ {T : C} (a b : R.obj T) (h : src.app T a = tgt.app T b),
          src.app T (comp a b h) = src.app T b) ∧
        (∀ {T : C} (a b : R.obj T) (h : src.app T a = tgt.app T b),
          tgt.app T (comp a b h) = tgt.app T a) ∧
        (∀ {T : C} (a b d : R.obj T)
            (h_ab : src.app T a = tgt.app T b) (h_bd : src.app T b = tgt.app T d)
            (h_ab_d : src.app T (comp a b h_ab) = tgt.app T d)
            (h_a_bd : src.app T a = tgt.app T (comp b d h_bd)),
          comp (comp a b h_ab) d h_ab_d = comp a (comp b d h_bd) h_a_bd) ∧
        (∀ {T : C} (x : U.obj T),
          ∃ (e : R.obj T), src.app T e = x ∧ tgt.app T e = x ∧
            (∀ (a : R.obj T) (h : src.app T a = tgt.app T e), comp a e h = a) ∧
              (∀ (a : R.obj T) (h : src.app T e = tgt.app T a), comp e a h = a)) ∧
        (∀ {T : C} (a : R.obj T),
          ∃ (i : R.obj T) (h_ai : src.app T a = tgt.app T i)
            (h_ia : src.app T i = tgt.app T a),
            (∀ (b : R.obj T) (h : src.app T b = tgt.app T (comp a i h_ai)),
                comp b (comp a i h_ai) h = b) ∧
              (∀ (b : R.obj T) (h : src.app T (comp a i h_ai) = tgt.app T b),
                comp (comp a i h_ai) b h = b) ∧
              (∀ (b : R.obj T) (h : src.app T b = tgt.app T (comp i a h_ia)),
                comp b (comp i a h_ia) h = b) ∧
              (∀ (b : R.obj T) (h : src.app T (comp i a h_ia) = tgt.app T b),
                comp (comp i a h_ia) b h = b)) ∧
        (∀ {T T' : C} (f : T ⟶ T') (a b : R.obj T)
            (h : src.app T a = tgt.app T b)
            (h' : src.app T' (R.map f a) = tgt.app T' (R.map f b)),
          R.map f (comp a b h) = comp (R.map f a) (R.map f b) h') :=
  sorry

namespace IsGroupoidInFunctors

/-- Source and target of a composite are the source of the earlier arrow and the target of
the later arrow. -/
theorem spec {C : Type u} [Category.{v} C] {U R : C ⥤ Type v} {src tgt : R ⟶ U}
    {comp : {T : C} → (a b : R.obj T) → src.app T a = tgt.app T b → R.obj T}
    [IsGroupoidInFunctors U R src tgt comp] {T : C}
    (a b : R.obj T) (h : src.app T a = tgt.app T b) :
    src.app T (comp a b h) = src.app T b ∧ tgt.app T (comp a b h) = tgt.app T a :=
  sorry

/-- Every object of the evaluation at `T` has an identity arrow. -/
theorem exists_id_obj {C : Type u} [Category.{v} C] {U R : C ⥤ Type v} {src tgt : R ⟶ U}
    {comp : {T : C} → (a b : R.obj T) → src.app T a = tgt.app T b → R.obj T}
    [IsGroupoidInFunctors U R src tgt comp] {T : C} (x : U.obj T) :
    ∃ (e : R.obj T), src.app T e = x ∧ tgt.app T e = x :=
  sorry

/-- Every arrow of the evaluation at `T` has an inverse. -/
theorem exists_inv_arrow {C : Type u} [Category.{v} C] {U R : C ⥤ Type v} {src tgt : R ⟶ U}
    {comp : {T : C} → (a b : R.obj T) → src.app T a = tgt.app T b → R.obj T}
    [IsGroupoidInFunctors U R src tgt comp] {T : C} (a : R.obj T) :
    ∃ (i : R.obj T), src.app T i = tgt.app T a ∧ tgt.app T i = src.app T a :=
  sorry

end IsGroupoidInFunctors

end CategoryTheory
