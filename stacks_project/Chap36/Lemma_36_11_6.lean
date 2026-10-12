/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure
open scoped CartesianClosed CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

/- Lemma 36.11.6 (1): a perfect derived module on a Noetherian scheme has coherent
cohomology and is bounded. -/
@[stacks 0FXU] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.boundedCoherentCohomology :
    ∀ {X : Scheme.{u}} [IsNoetherian X] {E : RingedSpace.ModuleDerived X.toRingedSpace}
      [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)],
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) E ∧
          (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) E)

/- Lemma 36.11.6 (2): derived tensoring a complex with coherent cohomology by a
perfect complex preserves coherent cohomology. -/
@[stacks 0FXU] #check (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.tensorCoherentCohomology :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    {E L : RingedSpace.ModuleDerived X.toRingedSpace}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)],
    RingedSpace.ModuleDerived.IsPerfect E →
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⊗ᴸ L))

/- Lemma 36.11.6 (3): derived internal Hom from a perfect complex to a complex with
coherent cohomology has coherent cohomology. -/
@[stacks 0FXU] #check (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.internalHomCoherentCohomology :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    {E L : RingedSpace.ModuleDerived X.toRingedSpace}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
    [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)],
    RingedSpace.ModuleDerived.IsPerfect E →
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
        DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⟹ L))

/- Lemma 36.11.6 (4): derived tensoring a bounded complex with coherent cohomology by
a perfect complex preserves bounded coherent cohomology. -/
@[stacks 0FXU] #check (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.tensorBoundedCoherentCohomology :
  ∀ {X : Scheme.{u}} [IsNoetherian X]
    {E L : RingedSpace.ModuleDerived X.toRingedSpace}
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)],
    RingedSpace.ModuleDerived.IsPerfect E →
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
        (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L →
          DerivedCategory.cohomologyIn
              (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⊗ᴸ L) ∧
            (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) (E ⊗ᴸ L))

/- Lemma 36.11.6 (5): derived internal Hom from a perfect complex to a bounded complex
with coherent cohomology has bounded coherent cohomology. -/
@[stacks 0FXU] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.internalHomBoundedCoherentCohomology :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      {E L : RingedSpace.ModuleDerived X.toRingedSpace}
      [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)],
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
          (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L →
            DerivedCategory.cohomologyIn
                (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⟹ L) ∧
              (t.bounded : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) (E ⟹ L))

/- Lemma 36.11.6 (6): derived tensoring a bounded-below complex with coherent
cohomology by a perfect complex preserves bounded-below coherent cohomology. -/
@[stacks 0FXU] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.tensorBoundedBelowCoherentCohomology :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      {E L : RingedSpace.ModuleDerived X.toRingedSpace}
      [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)],
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
          (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L →
            DerivedCategory.cohomologyIn
                (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⊗ᴸ L) ∧
              (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) (E ⊗ᴸ L))

/- Lemma 36.11.6 (7): derived internal Hom from a perfect complex to a bounded-below
complex with coherent cohomology has bounded-below coherent cohomology. -/
@[stacks 0FXU] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.internalHomBoundedBelowCoherentCohomology :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      {E L : RingedSpace.ModuleDerived X.toRingedSpace}
      [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)],
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
          (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L →
            DerivedCategory.cohomologyIn
                (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⟹ L) ∧
              (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) (E ⟹ L))

/- Lemma 36.11.6 (8): derived tensoring a bounded-above complex with coherent
cohomology by a perfect complex preserves bounded-above coherent cohomology. -/
@[stacks 0FXU] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.tensorBoundedAboveCoherentCohomology :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      {E L : RingedSpace.ModuleDerived X.toRingedSpace}
      [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)],
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
          (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L →
            DerivedCategory.cohomologyIn
                (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⊗ᴸ L) ∧
              (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) (E ⊗ᴸ L))

/- Lemma 36.11.6 (9): derived internal Hom from a perfect complex to a bounded-above
complex with coherent cohomology has bounded-above coherent cohomology. -/
@[stacks 0FXU] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect.internalHomBoundedAboveCoherentCohomology :
    ∀ {X : Scheme.{u}} [IsNoetherian X]
      {E L : RingedSpace.ModuleDerived X.toRingedSpace}
      [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
      [MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      [MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)],
      RingedSpace.ModuleDerived.IsPerfect E →
        DerivedCategory.cohomologyIn
            (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
          (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L →
            DerivedCategory.cohomologyIn
                (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) (E ⟹ L) ∧
              (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) (E ⟹ L))
