module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect

@[expose] public section

open CategoryTheory
open DerivedCategory.TStructure

universe u

/- Lemma 36.27.1: if `f : X ⟶ S` is locally of finite type with `S` Noetherian,
and `E` has bounded coherent cohomology, degreewise proper support over `S`, and finite Tor
dimension over `f⁻¹𝒪_S`, then its derived pushforward is perfect. -/
@[stacks 08EV] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_isPerfect_of_finiteTorDimension :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsNoetherian S] [AlgebraicGeometry.LocallyOfFiniteType f]
      [DerivedCategory.DerivedTensor.Right.Has
        (C := AlgebraicGeometry.RingedSpace.Modules
          (AlgebraicGeometry.RingedSpace.Hom.inverseImageBase f.toShHom))]
      (E : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)
      (hE_coherent : DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E)
      (hE_bounded : (t.bounded : ObjectProperty
        (AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace)) E)
      [∀ i : ℤ, AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f
        (AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf E i)]
      (hE_tor : AlgebraicGeometry.RingedSpace.HasFiniteTorDimension
        ((AlgebraicGeometry.RingedSpace.ModuleDerived.relativeRestriction f.toShHom).obj E)),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
        ((AlgebraicGeometry.RingedSpace.moduleDerivedPushforward f.toShHom).obj E))
