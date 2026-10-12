/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.InternalHom.Coherent
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.MonoidalClosed
open DerivedCategory.TStructure

universe u

/- Lemma 36.11.5: on a locally Noetherian scheme, derived internal Hom from an object with
bounded-above coherent cohomology to an object with bounded-below coherent cohomology has
bounded-below coherent cohomology. -/
@[stacks 0D0C] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.InternalHom.boundedBelowCoherentCohomology :
    ∀ {X : Scheme.{u}}
      [IsLocallyNoetherian X]
      [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.TensorDescends X.toRingedSpace]
      [RingedSpace.ModuleDerived.KFlat.IsLocalization X.toRingedSpace]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (K L : RingedSpace.ModuleDerived X.toRingedSpace),
      DerivedCategory.cohomologyIn
          (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) K →
        (t.minus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) K →
          DerivedCategory.cohomologyIn
              (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf) L →
            (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)) L →
              DerivedCategory.cohomologyIn
                  (SheafOfModules.isCoherent X.toRingedSpace.ringCatSheaf)
                  ((ihomOf H K).obj L) ∧
                (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))
                  ((ihomOf H K).obj L))
