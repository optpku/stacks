/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.RingHom
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.Algebra.Homology.DerivedCategory.Perfect

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.DerivedCoextension

variable {R A : Type u} [CommRing R] [CommRing A]

/-- For a commutative ring homomorphism with perfect target module, derived coextension is
isomorphic to derived tensor change of rings with the coextension of the source regular module.
-/
theorem isomorphicTensorDualOfPerfect (f : R →+* A)
    (hA : ModuleCat.IsPerfect f.targetModule) :
    IsIsomorphic (derivedCoextensionOfScalars f)
      (derivedTensorChangeOfRings f
        ((derivedCoextensionOfScalars f).obj
          (ModuleCat.single0 (ModuleCat.of R R)))) := sorry

/-- For every derived source module, the value of derived coextension for a perfect target
module is isomorphic to the corresponding derived tensor change-of-rings value. -/
theorem objIsomorphicTensorDualOfPerfect (f : R →+* A)
    (hA : ModuleCat.IsPerfect f.targetModule)
    (K : DerivedCategory (ModuleCat R)) :
    IsIsomorphic ((derivedCoextensionOfScalars f).obj K)
      ((derivedTensorChangeOfRings f
        ((derivedCoextensionOfScalars f).obj
          (ModuleCat.single0 (ModuleCat.of R R)))).obj K) := sorry

end CategoryTheory.ModuleCat.DerivedCoextension
