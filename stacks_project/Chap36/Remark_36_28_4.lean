/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.ExtRepresentability.BaseChange

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory DerivedCategory.TStructure
open CategoryTheory.MonoidalClosed
open RingedSpace.Module.Derived RingedSpace.ModuleDerived

noncomputable section

universe u

/- Remark 36.28.4: an explicit pseudo-coherent Ext representative remains a
representation after cartesian base change; `E` and `L` are pulled back in the
derived category, while `G` is pulled back termwise as an ordinary complex. -/
@[stacks 0DJS] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.RepresentsExt.pullback :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
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
      [∀ n : ℤ, AlgebraicGeometry.Scheme.Modules.HasProperSupportOver f
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
      (hrep : AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.RepresentsExt
        f E.obj G L)
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
      [MonoidalClosed (RingedSpace.ModuleDerived S'.toRingedSpace)],
      -- Local instance justification (proof-local temporary data): cartesianness supplies this termwise relative-flatness instance.
      letI : ∀ n : ℤ, SheafOfModules.IsFlatOver
          ((((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj G).X n) f'.toShHom :=
        fun n => AlgebraicGeometry.Scheme.Modules.isFlatOver_pullback_of_isPullback
          g' f' f g sq (G.X n)
      AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.RepresentsExt f'
        ((RingedSpace.modulePullbackDerived g'.toShHom).obj E.obj)
        (((RingedSpace.Hom.pullback g'.toShHom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj G)
        ((RingedSpace.modulePullbackDerived g.toShHom).obj L))
