module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.Perfect.InternalHom

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.RingedSpace.ModuleDerived
open CategoryTheory.DerivedCategory
open CategoryTheory.MonoidalClosed
open scoped CartesianClosed

noncomputable section

universe u

/- Lemma 36.27.3: for a locally finite type morphism `f : X ⟶ S` to a Noetherian
scheme, the derived pushforward of the derived internal Hom from a perfect object to a
bounded, termwise coherent and relatively flat complex with cohomologically proper support
over `S` is perfect. -/
@[stacks 0DJR]
#check (AlgebraicGeometry.Scheme.ModuleDerived.pushforward_internalHom_isPerfect :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [LocallyOfFiniteType f]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (hE : RingedSpace.ModuleDerived.IsPerfect E)
    (G : CochainComplex X.Modules ℤ)
    (hG_bounded : CochainComplex.bounded X.Modules G)
    [∀ i : ℤ, (G.X i).IsCoherent]
    [∀ i : ℤ, SheafOfModules.IsFlatOver (G.X i) f.toShHom]
    [∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
      (RingedSpace.ModuleDerived.cohomologySheaf (DerivedCategory.Q.obj G) i)],
    RingedSpace.ModuleDerived.IsPerfect
      ((RingedSpace.moduleDerivedPushforward f.toShHom).obj
        (E ⟹ DerivedCategory.Q.obj G)))
