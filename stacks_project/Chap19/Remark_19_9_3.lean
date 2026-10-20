module

public import Mathlib.CategoryTheory.Abelian.FreydMitchell
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe v u

variable (C : Type u) [Category.{v} C] [Abelian C]

/- Remark 19.9.3: the Freyd-Mitchell embedding theorem is the canonical mathlib theorem
`CategoryTheory.Abelian.freyd_mitchell`, asserting that every abelian category admits a fully
faithful exact functor to a category of modules over a ring. This is stronger than
Lemma `19.9.2`, but the sheaf-theoretic embedding from that lemma is the one used in the Stacks
Project for diagram chasing in abelian sheaf categories. -/
@[stacks 05PP] #check
  (freyd_mitchell C :
    ∃ (R : Type (max u v)) (_ : Ring R) (F : C ⥤ ModuleCat.{max u v} R),
      F.Full ∧ F.Faithful ∧ PreservesFiniteLimits F ∧ PreservesFiniteColimits F)
