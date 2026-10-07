module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.EffectiveCartierDuality

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open AlgebraicGeometry.Scheme.EffectiveCartierDuality

universe u

/- Lemma 48.14.2: for an effective Cartier divisor `i : D ⟶ X`, the canonical map
`Li^*K ⊗ᴸ normalSheaf(i)[-1] ⟶ RHom(𝒪_D, K)` is an isomorphism functorial in
`K ∈ D(𝒪_X)`. -/
@[stacks 0AA4] #check
  (AlgebraicGeometry.Scheme.EffectiveCartierDuality.comparisonIsIso :
    ∀ {X D : Scheme.{u}} (i : D ⟶ X) [IsEffectiveCartierDivisor i]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [KFlat.HomotopyTensorDescends D.toRingedSpace]
      [KFlat.TensorDescends D.toRingedSpace]
      [KFlat.IsLocalization D.toRingedSpace]
      [RingedSite.Hom.DerivedAdjunction.HasPair
        (RingedSpace.opensRingedSiteHom i.toShHom)]
      [Functor.HasLeftDerivedFunctor
        (RingedSpace.modulePullbackToDerived i.toShHom)
        (RingedSpace.ModuleQis X.toRingedSpace)]
      [HasWeakSheafify (Opens.grothendieckTopology D.toRingedSpace) AddCommGrpCat.{u}]
      [(Opens.grothendieckTopology D.toRingedSpace).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
      [Functor.Monoidal (RingedSpace.modulePullbackDerived i.toShHom)]
      (rHomOD : RingedSpace.ModuleDerived X.toRingedSpace ⥤
        RingedSpace.ModuleDerived D.toRingedSpace)
      (rHomODAdjunction :
        RingedSpace.moduleDerivedPushforward i.toShHom ⊣ rHomOD)
      (structureSheafUnitIso :
        (DerivedCategory.singleFunctor X.Modules 0).obj
            (SheafOfModules.unit X.ringCatSheaf) ≅
          𝟙_ (RingedSpace.ModuleDerived X.toRingedSpace))
      (normalIdentification :
        rHomOD.obj ((DerivedCategory.singleFunctor X.Modules 0).obj
            (SheafOfModules.unit X.ringCatSheaf)) ≅ normalShift i),
    IsIso (comparison i rHomOD rHomODAdjunction structureSheafUnitIso normalIdentification))
