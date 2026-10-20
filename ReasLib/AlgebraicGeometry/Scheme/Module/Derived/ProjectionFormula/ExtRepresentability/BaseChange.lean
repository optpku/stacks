module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.Ext.Representation
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.ExtRepresentability
public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.BaseChange

/-!
# Base change of Ext representations

This module records preservation of pseudo-coherent Ext representations under cartesian base
change of schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory DerivedCategory.TStructure
open CategoryTheory.MonoidalClosed
open RingedSpace.Module.Derived RingedSpace.ModuleDerived

noncomputable section

universe u

namespace AlgebraicGeometry
namespace Scheme
namespace ModuleDerived
namespace ProjectionFormula
namespace RepresentsExt

/-- An explicit pseudo-coherent representation of an Ext delta functor remains a representation
after cartesian base change. The coefficient complex is pulled back termwise as an ordinary
complex. -/
theorem pullback
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsNoetherian S] [LocallyOfFiniteType f]
    (E : DerivedCategory.CohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
    (G : CochainComplex X.Modules ℤ)
    (hE_boundedAbove :
      (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj)
    (hE_coherent : DerivedCategory.cohomologyIn
      (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E.obj)
    (hG_bounded : CochainComplex.bounded X.Modules G)
    [∀ n : ℤ, (G.X n).IsCoherent]
    [∀ n : ℤ, SheafOfModules.IsFlatOver (G.X n) f.toShHom]
    [∀ n : ℤ, Scheme.Modules.HasProperSupportOver f
      (RingedSpace.ModuleDerived.cohomologySheaf (DerivedCategory.Q.obj G) n)]
    [KFlat.HomotopyTensorDescends X.toRingedSpace]
    [KFlat.TensorDescends X.toRingedSpace]
    [KFlat.IsLocalization X.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
    [KFlat.HomotopyTensorDescends S.toRingedSpace]
    [KFlat.TensorDescends S.toRingedSpace]
    [KFlat.IsLocalization S.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
    (L : RingedSpace.ModuleDerived S.toRingedSpace)
    (hL : RingedSpace.ModuleDerived.IsPseudoCoherent L)
    (hrep : ProjectionFormula.RepresentsExt f E.obj G L)
    {X' S' : Scheme.{u}}
    (g' : X' ⟶ X) (f' : X' ⟶ S') (g : S' ⟶ S)
    (sq : IsPullback g' f' f g)
    [KFlat.HomotopyTensorDescends X'.toRingedSpace]
    [KFlat.TensorDescends X'.toRingedSpace]
    [KFlat.IsLocalization X'.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived X'.toRingedSpace)]
    [KFlat.HomotopyTensorDescends S'.toRingedSpace]
    [KFlat.TensorDescends S'.toRingedSpace]
    [KFlat.IsLocalization S'.toRingedSpace]
    [MonoidalClosed (RingedSpace.ModuleDerived S'.toRingedSpace)] :
    -- Local instance justification (proof-local temporary data): cartesianness supplies this termwise relative-flatness instance.
    letI : ∀ n : ℤ, SheafOfModules.IsFlatOver
        ((((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G).X n) f'.toShHom :=
      fun n => Scheme.Modules.isFlatOver_pullback_of_isPullback
        g' f' f g sq (G.X n)
    ProjectionFormula.RepresentsExt f'
      ((RingedSpace.modulePullbackDerived g'.toShHom).obj E.obj)
      (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj G)
      ((RingedSpace.modulePullbackDerived g.toShHom).obj L) := sorry

end RepresentsExt
end ProjectionFormula
end ModuleDerived
end Scheme
end AlgebraicGeometry
