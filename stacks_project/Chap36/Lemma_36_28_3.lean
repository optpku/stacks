/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.ProjectionFormula.ExtRepresentability
public import stacks_project.Chap36.Lemma_36_10_3

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.DerivedCategory DerivedCategory.TStructure
open CategoryTheory.MonoidalClosed
open RingedSpace.Module.Derived RingedSpace.ModuleDerived

noncomputable section

universe u

/- Lemma 36.28.3 (1): through every degree `m`, Ext against the bounded-above
coherent object `E` is naturally approximated by tensoring with a perfect object
on `S`, compatibly with connecting maps. -/
@[stacks 08IF] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.existsPerfectExtApproximation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [IsNoetherian S] [LocallyOfFiniteType f]
      (E : DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
      (hE_boundedAbove :
        (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj)
      (hE_coherent : DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E.obj)
      (G : CochainComplex X.Modules ℤ)
      (hG_bounded : CochainComplex.bounded X.Modules G)
      [∀ i : ℤ, (G.X i).IsCoherent]
      [∀ i : ℤ, SheafOfModules.IsFlatOver (G.X i) f.toShHom]
      [∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
        (RingedSpace.ModuleDerived.cohomologySheaf (DerivedCategory.Q.obj G) i)]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [KFlat.HomotopyTensorDescends S.toRingedSpace]
      [KFlat.TensorDescends S.toRingedSpace]
      [KFlat.IsLocalization S.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)]
      (m : ℤ),
      ∃ (K : RingedSpace.ModuleDerived S.toRingedSpace)
        (hK : RingedSpace.ModuleDerived.IsPerfect K)
        (α : AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.CohomologyTransform
          (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.extDelta f E.obj G)
          (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.tensorDelta S K)),
        ∀ i : ℤ, i ≤ m → IsIso (α.app i))

/- Lemma 36.28.3 (2): Ext against the bounded-above coherent object `E` is
naturally represented in every degree by a pseudo-coherent object on `S`,
compatibly with connecting maps. -/
@[stacks 08IF] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.existsPseudoCoherentExtRepresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S)
      [IsNoetherian S] [LocallyOfFiniteType f]
      (E : DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace))
      (hE_boundedAbove :
        (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E.obj)
      (hE_coherent : DerivedCategory.cohomologyIn
        (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E.obj)
      (G : CochainComplex X.Modules ℤ)
      (hG_bounded : CochainComplex.bounded X.Modules G)
      [∀ i : ℤ, (G.X i).IsCoherent]
      [∀ i : ℤ, SheafOfModules.IsFlatOver (G.X i) f.toShHom]
      [∀ i : ℤ, Scheme.Modules.HasProperSupportOver f
        (RingedSpace.ModuleDerived.cohomologySheaf (DerivedCategory.Q.obj G) i)]
      [KFlat.HomotopyTensorDescends X.toRingedSpace]
      [KFlat.TensorDescends X.toRingedSpace]
      [KFlat.IsLocalization X.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)]
      [KFlat.HomotopyTensorDescends S.toRingedSpace]
      [KFlat.TensorDescends S.toRingedSpace]
      [KFlat.IsLocalization S.toRingedSpace]
      [MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace)],
      ∃ (L : RingedSpace.ModuleDerived S.toRingedSpace)
        (hL : RingedSpace.ModuleDerived.IsPseudoCoherent L)
        (α : AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.CohomologyTransform
          (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.representedExtDelta S L)
          (AlgebraicGeometry.Scheme.ModuleDerived.ProjectionFormula.extDelta f E.obj G)),
        ∀ i : ℤ, IsIso (α.app i))
