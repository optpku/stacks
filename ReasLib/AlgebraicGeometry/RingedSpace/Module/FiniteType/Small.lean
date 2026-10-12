/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteType
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent

/-!
# Smallness of finite-type quasi-coherent modules

Finite-type quasi-coherent module sheaves on a ringed space form an essentially small
object property.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u})

/-- Finite-type quasi-coherent module sheaves on a ringed space form an essentially small
object property. -/
instance finiteTypeQuasicoherent_essentiallySmall :
    ObjectProperty.EssentiallySmall.{u + 1}
      ((SheafOfModules.IsFiniteType (R := X.ringCatSheaf) : ObjectProperty X.Modules) ⊓
        X.quasiCoherentModuleProperty) :=
  ObjectProperty.EssentiallySmall.of_le
    (Q := (SheafOfModules.IsFiniteType (R := X.ringCatSheaf) : ObjectProperty X.Modules))
    inf_le_left

end AlgebraicGeometry.RingedSpace
