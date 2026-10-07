module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import StacksCheckRecall

@[expose] public section

universe uC vC w

/- Definition 59.17.2: For a ringed site with structure sheaf O, an O-module sheaf is
quasi-coherent when it is locally the cokernel of a map between free O-module sheaves. -/
@[stacks 03OH]
#check (@SheafOfModules.IsQuasicoherent :
  ∀ {C : Type uC} [CategoryTheory.Category.{vC} C]
    {J : CategoryTheory.GrothendieckTopology C}
    {R : CategoryTheory.Sheaf J RingCat.{w}}
    [∀ X : C, CategoryTheory.HasWeakSheafify (J.over X) AddCommGrpCat.{w}]
    [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}],
    SheafOfModules.{w} R → Prop)
