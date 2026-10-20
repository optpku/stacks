module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Functoriality

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex

universe u

#check (SheafOfModules.RingedSite.CotangentComplex.map :
  ∀ {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify J CommRingCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}],
    ∀ {A : Sheaf J CommRingCat.{u}} {B B' : Under A} (h : B ⟶ B'),
      ((SheafOfModules.ChangeOfRings.extendScalars (ringSheafMap h.right)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (obj A B) ⟶
        obj A B')
