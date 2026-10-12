/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.HomotopyCategory.Perfect
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect.Subcategory
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable (R : Type u) [Ring R]

/- Definition 64.10.1 (1): K_perf(Λ) is the homotopy category of bounded complexes of finite
projective left Λ-modules. -/
@[stacks 03TH] #check (HomotopyCategory.Perfect R : Type (u + 1))

/- Definition 64.10.1 (2): the functor K_perf(Λ) ⟶ D(Λ) is fully faithful. -/
@[stacks 03TH] #check (HomotopyCategory.Perfect.toDerived R :
  HomotopyCategory.Perfect R ⥤ DerivedCategory (ModuleCat.{u} R))
#check (HomotopyCategory.Perfect.instFullToDerived R :
  (HomotopyCategory.Perfect.toDerived R).Full)
#check (HomotopyCategory.Perfect.instFaithfulToDerived R :
  (HomotopyCategory.Perfect.toDerived R).Faithful)

/- Definition 64.10.1 (3): D_perf(Λ) is the essential image of that functor. -/
@[stacks 03TH] #check (CategoryTheory.PerfectDerived R : Type (u + 1))
#check (HomotopyCategory.Perfect.mem_essImage_toDerived_iff R :
  ∀ K : DerivedCategory (ModuleCat.{u} R),
    (HomotopyCategory.Perfect.toDerived R).essImage K ↔ K.IsPerfect)

/- Definition 64.10.1 (4): an object of D(Λ) is called perfect if it lies in D_perf(Λ). -/
@[stacks 03TH] #check (DerivedCategory.IsPerfect :
  DerivedCategory (ModuleCat.{u} R) → Prop)
