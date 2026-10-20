module

public import ReasLib.CategoryTheory.DerivedCategory.Preimage.Lift.Operations
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Laws for selected-preimage lifts

Selected-preimage lifts satisfy the expected equality-transport, identity, and associativity laws.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe w v u

namespace CategoryTheory.DerivedCategory.Preimage.Lift

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- Transport along reflexivity fixes a selected-preimage lift. -/
@[simp, stacks 0BKM "reflexive transport of a selected-preimage lift"]
theorem reindex_rfl
    {K L : DerivedCategory A} {f : K ⟶ L} (l : Lift f) :
    reindex rfl l = l := sorry

/-- Successive transports of a selected-preimage lift combine by equality transitivity. -/
@[simp, stacks 0BKM "transitivity of selected-preimage lift transport"]
theorem reindex_trans
    {K L : DerivedCategory A} {f f' f'' : K ⟶ L}
    (e : f = f') (e' : f' = f'') (l : Lift f) :
    reindex e' (reindex e l) = reindex (e.trans e') l := sorry

/-- Transport along an equality and its inverse fixes a selected-preimage lift. -/
@[simp, stacks 0BKM "inverse transport of a selected-preimage lift"]
theorem reindex_symm
    {K L : DerivedCategory A} {f f' : K ⟶ L}
    (e : f = f') (l : Lift f) :
    reindex e.symm (reindex e l) = l := sorry

/-- Reindexing the left factor of a composite selected-preimage lift commutes with composition. -/
@[simp, stacks 0BKM "left-factor transport of selected-preimage lifts"]
theorem reindex_comp_left
    {K L M : DerivedCategory A} {f f' : K ⟶ L} {g : L ⟶ M}
    (e : f = f') (l : Lift f) (m : Lift g) :
    reindex (congrArg (fun k : K ⟶ L => k ≫ g) e) (comp l m) =
      comp (reindex e l) m := sorry

/-- Reindexing the right factor of a composite selected-preimage lift commutes with composition. -/
@[simp, stacks 0BKM "right-factor transport of selected-preimage lifts"]
theorem reindex_comp_right
    {K L M : DerivedCategory A} {f : K ⟶ L} {g g' : L ⟶ M}
    (e : g = g') (l : Lift f) (m : Lift g) :
    reindex (congrArg (fun k : L ⟶ M => f ≫ k) e) (comp l m) =
      comp l (reindex e m) := sorry

/-- Reindexing both factors of a composite selected-preimage lift commutes with composition. -/
@[simp, stacks 0BKM "two-factor transport of selected-preimage lifts"]
theorem reindex_comp
    {K L M : DerivedCategory A} {f f' : K ⟶ L} {g g' : L ⟶ M}
    (e : f = f') (e' : g = g') (l : Lift f) (m : Lift g) :
    reindex (congrArg₂ (fun (a : K ⟶ L) (b : L ⟶ M) => a ≫ b) e e') (comp l m) =
      comp (reindex e l) (reindex e' m) := sorry

/-- Identity is a left unit for composition of selected-preimage lifts. -/
@[stacks 0BKM "left identity law for selected-preimage lifts"]
theorem id_comp
    {K L : DerivedCategory A} {f : K ⟶ L} (l : Lift f) :
    reindex (Category.id_comp f) (comp (id K) l) = l := sorry

/-- Identity is a right unit for composition of selected-preimage lifts. -/
@[stacks 0BKM "right identity law for selected-preimage lifts"]
theorem comp_id
    {K L : DerivedCategory A} {f : K ⟶ L} (l : Lift f) :
    reindex (Category.comp_id f) (comp l (id L)) = l := sorry

/-- Composition of selected-preimage lifts is associative after the canonical transport. -/
@[stacks 0BKM "associativity law for selected-preimage lifts"]
theorem assoc
    {K L M N : DerivedCategory A} {f : K ⟶ L} {g : L ⟶ M} {h : M ⟶ N}
    (l : Lift f) (m : Lift g) (n : Lift h) :
    reindex (Category.assoc f g h) (comp (comp l m) n) =
      comp l (comp m n) := sorry

end CategoryTheory.DerivedCategory.Preimage.Lift
