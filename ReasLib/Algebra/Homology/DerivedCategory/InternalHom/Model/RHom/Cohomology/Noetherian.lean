/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.InjectiveAmplitude
public import ReasLib.Algebra.Homology.DerivedCategory.InternalHom.Model.RHom.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.RingTheory.Noetherian.Defs

@[expose] public section

universe u

namespace CategoryTheory.DerivedCategory.InternalHom.RHom

/-- Over a Noetherian commutative ring, canonical derived Hom has finite cohomology when
both arguments have finite cohomology and the target has finite injective dimension. -/
theorem finiteCohomology_of_finiteInjectiveDimension
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (K L : DerivedCategory (ModuleCat.{u} A))
    (hK : DerivedCategory.cohomologyIn (ModuleCat.isFG A) K)
    (hL : DerivedCategory.cohomologyIn (ModuleCat.isFG A) L)
    (hL_injective : DerivedCategory.HasFiniteInjectiveDimension L) :
    DerivedCategory.cohomologyIn (ModuleCat.isFG A) (RHom.obj K L) := sorry

end CategoryTheory.DerivedCategory.InternalHom.RHom
