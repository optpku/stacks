/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FiniteType.Small
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

/- Lemma 95.5.2 (1): the category of finite-type `𝒪_X`-modules has a set of isomorphism
classes, with a representative family indexed in `Type u`. -/
@[stacks 04U5]
#check
  (CategoryTheory.ObjectProperty.EssentiallySmall.exists_family_representatives
    (SheafOfModules.IsFiniteType (R := X.ringCatSheaf) : ObjectProperty X.Modules) :
    ∃ (T : Type u) (F : T → X.Modules),
      (∀ t, (F t).IsFiniteType) ∧
      ∀ M : X.Modules, M.IsFiniteType →
        ∃ t, Nonempty (F t ≅ M))

/- Lemma 95.5.2 (2): the category of finite-type quasi-coherent `𝒪_X`-modules has a set of
isomorphism classes, with a representative family indexed in `Type u`. -/
@[stacks 04U5]
#check
  (CategoryTheory.ObjectProperty.EssentiallySmall.exists_family_representatives
    ((SheafOfModules.IsFiniteType (R := X.ringCatSheaf) : ObjectProperty X.Modules) ⊓
      X.quasiCoherentModuleProperty) :
    ∃ (T : Type u) (F : T → X.Modules),
      (∀ t, (F t).IsFiniteType ∧ (F t).IsQuasicoherent) ∧
      ∀ M : X.Modules, M.IsFiniteType ∧ M.IsQuasicoherent →
        ∃ t, Nonempty (F t ≅ M))

end AlgebraicGeometry.RingedSpace
