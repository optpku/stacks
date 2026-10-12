/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CohomologyIn
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/-- Derived modules on a scheme whose cohomology is quasi-coherent admit coproducts indexed
by types in the scheme's universe. -/
instance hasCoproducts (X : Scheme.{u}) :
    HasCoproducts.{u}
      (DerivedCategory.CohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)) := sorry

/-- The inclusion of derived modules with quasi-coherent cohomology into all derived modules
preserves coproducts indexed by types in the scheme's universe. -/
instance inclusionPreservesCoproducts (X : Scheme.{u}) (I : Type u) :
    PreservesColimitsOfShape (Discrete I)
      (Scheme.ModuleDerived.Quasicoherent.inclusion X) := sorry

end AlgebraicGeometry.Scheme.DerivedQCoh
