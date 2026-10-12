/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Tensor.ChangeOfRings
public import ReasLib.RingTheory.RingHom.Perfect.Basic

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

variable {R A : Type u} [CommRing R] [CommRing A]
  [IsNoetherianRing R] [IsNoetherianRing A]
variable (f : R →+* A) (p : Presentation f)

/-- A presentation-defined upper-shriek functor for a perfect homomorphism of Noetherian
rings is naturally isomorphic to derived tensoring with its value on the base ring. -/
theorem isomorphicTensorDualOfPerfect [f.IsPerfectRingMap] :
    IsIsomorphic p.functor
      (derivedTensorChangeOfRings f
        (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))) := sorry

/-- At every derived module, a presentation-defined upper-shriek functor for a perfect
homomorphism of Noetherian rings is isomorphic to derived tensoring with its value on the
base ring. -/
theorem objIsomorphicTensorDualOfPerfect [f.IsPerfectRingMap]
    (K : DerivedCategory (ModuleCat.{u, u} R)) :
    IsIsomorphic (p.functor.obj K)
      ((derivedTensorChangeOfRings f
        (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))).obj K) := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
