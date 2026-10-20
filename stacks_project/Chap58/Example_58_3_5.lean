module

public import ReasLib.CategoryTheory.Galois.Action
public import Mathlib.CategoryTheory.Galois.Topology
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

/- Example 58.3.5: If F : C ⥤ Sets takes finite values, Aut(F) is canonically a
profinite topological group (Lemma 58.3.1), and X ↦ F(X) with the induced Aut(F)-action
is a functor C ⟶ Finite-G-Sets whose action is continuous for that topology. -/
@[stacks 0BMW] #check (CategoryTheory.PreGaloisCategory.finiteActionFunctor :
  {C : Type u} → [Category.{v} C] → (F : C ⥤ FintypeCat.{w}) →
    C ⥤ Action FintypeCat.{w} (Aut F))

#check PreGaloisCategory.finiteActionFunctor_comp_forget₂_eq
#check PreGaloisCategory.continuousSMul_aut_fiber
#check
  (fun {C : Type u} [Category.{v} C] (F : C ⥤ FintypeCat.{w}) ↦
    ProfiniteGrp.of (Aut F))
