module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.CompletionRestriction

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.DerivedCoextension

noncomputable section

universe u

/- Lemma 52.6.6: for `alpha : O ⟶ O'`, the inverse image of the objects derived complete
with respect to `I` under derived restriction of scalars is precisely the class of objects
derived complete with respect to the extended ideal `I O'`. -/
@[stacks 099C] #check
  (RingedSite.Hom.ModuleDerived.derivedCompleteObjectProperty_inverseImage :
    ∀ {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
      [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
      [HasWeakSheafify J AddCommGrpCat.{u}]
      [HasSheafify J AddCommGrpCat.{u}]
      [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
      {O O' : Sheaf J CommRingCat.{u}}
      (alpha : O ⟶ O') (I : Subobject (unitModule J O)),
        (RingedSite.Hom.ModuleDerived.derivedCompleteObjectProperty I).inverseImage
            (SheafOfModules.RingedSite.DerivedCoextension.restriction alpha) =
          RingedSite.Hom.ModuleDerived.derivedCompleteObjectProperty
            (SheafOfModules.RingedSite.IdealSheaf.extension I alpha))
