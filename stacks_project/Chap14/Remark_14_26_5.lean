/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyCategory
import StacksCheckRecall

@[expose] public section

/-!
@stack 08RJ

# Source-facing bridge for Remark 14.26.5

The homotopy category of simplicial objects is the categorical quotient by the reusable
zigzag homotopy congruence owned by ReasLib.
-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
variable {U V X W : SimplicialObject C} {a a' : U ⟶ V}
variable (h : SimplicialObject.Homotopic a a') (b : V ⟶ W) (c : X ⟶ U)

/- Remark 14.26.5 (1): postcomposition preserves simplicial homotopy. -/
@[stacks 08RJ "Remark 14.26.5 (1): postcomposition"]
#check (h.postcomp b : SimplicialObject.Homotopic (a ≫ b) (a' ≫ b))

/- Remark 14.26.5 (2): precomposition preserves simplicial homotopy. -/
@[stacks 08RJ "Remark 14.26.5 (2): precomposition"]
#check (h.precomp c : SimplicialObject.Homotopic (c ≫ a) (c ≫ a'))

/- Remark 14.26.5 (3): simultaneous precomposition and postcomposition preserve homotopy. -/
@[stacks 08RJ "Remark 14.26.5 (3): two-sided composition"]
#check (h.precomp_postcomp c b :
  SimplicialObject.Homotopic (c ≫ a ≫ b) (c ≫ a' ≫ b))

/- Remark 14.26.5 (4): quotienting morphisms by this congruence gives the simplicial homotopy
category and its canonical functor. -/
@[stacks 08RJ "Remark 14.26.5 (4): homotopy category"]
#check (SimplicialObject.HomotopyCategory C)

@[stacks 08RJ "Remark 14.26.5 (4): quotient functor"]
#check (SimplicialObject.HomotopyCategory.quotient C :
  SimplicialObject C ⥤ SimplicialObject.HomotopyCategory C)

/- Equality in the quotient is exactly simplicial homotopy. -/
@[stacks 08RJ "Remark 14.26.5: quotient equality"]
#check (SimplicialObject.HomotopyCategory.quotient.map_eq_iff a a' :
  (SimplicialObject.HomotopyCategory.quotient C).map a =
      (SimplicialObject.HomotopyCategory.quotient C).map a' ↔
    SimplicialObject.Homotopic a a')

/- The canonical quotient is surjective on morphisms and essentially surjective on objects. -/
@[stacks 08RJ "Remark 14.26.5: quotient surjectivity"]
#check (CategoryTheory.Quotient.full_functor (SimplicialObject.homotopyRel C) :
  (SimplicialObject.HomotopyCategory.quotient C).Full)

@[stacks 08RJ "Remark 14.26.5: quotient essential surjectivity"]
#check (CategoryTheory.Quotient.essSurj_functor (SimplicialObject.homotopyRel C) :
  (SimplicialObject.HomotopyCategory.quotient C).EssSurj)
