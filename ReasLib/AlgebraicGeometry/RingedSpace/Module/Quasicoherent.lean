/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
import Mathlib.Tactic.CrossRefAttribute

/-!
# Quasicoherent modules on a ringed space

This file provides the ringed-space-level name for the full subcategory of quasicoherent module
sheaves.  The defining predicate remains `SheafOfModules.IsQuasicoherent`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RingedSpace

/-- The canonical object property of quasicoherent module sheaves on a ringed space. -/
@[stacks 01BE "ringed-space quasicoherent module property"]
abbrev quasiCoherentModuleProperty (X : RingedSpace.{u}) : ObjectProperty X.Modules :=
  SheafOfModules.isQuasicoherent X.ringCatSheaf

/-- The category of quasicoherent module sheaves on `X`. -/
@[stacks 01BE "quasicoherent module category"]
abbrev QCoh (X : RingedSpace.{u}) :=
  (quasiCoherentModuleProperty X).FullSubcategory

namespace QCoh

/-- The inclusion of quasicoherent modules into all module sheaves on a ringed space. -/
@[stacks 01BE "ringed-space quasicoherent module inclusion"]
abbrev inclusion (X : RingedSpace.{u}) : QCoh X ⥤ X.Modules :=
  (quasiCoherentModuleProperty X).ι

end QCoh

end AlgebraicGeometry.RingedSpace

namespace AlgebraicGeometry

/-- An infinite coproduct of quasi-coherent module sheaves need not be
quasi-coherent. -/
@[stacks 02CF "infinite coproduct"]
theorem existsInfiniteCoproductNotQuasicoherent :
    ∃ (X : RingedSpace.{u}) (I : Type u) (_ : Infinite I)
      (F : I → RingedSpace.Modules X),
      (∀ i, (F i).IsQuasicoherent) ∧ ¬ (∐ F).IsQuasicoherent := sorry

end AlgebraicGeometry
