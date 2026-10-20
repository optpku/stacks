/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek.Perfect
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.Tensor.Right.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import ReasLib.RingTheory.RingHom.Perfect.CompleteIntersection

@[expose] public section

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

variable {R A : Type u} [CommRing R] [CommRing A]
  [IsNoetherianRing R] [IsNoetherianRing A]
variable (f : R →+* A) (p : Presentation f)

/-- The value on the base ring of a presentation-defined upper-shriek functor for a local
complete-intersection homomorphism of Noetherian rings is tensor-invertible when the ambient
tensor model identifies the chosen monoidal tensor with canonical derived tensoring. -/
theorem isInvertibleObject_of_isLocalCompleteIntersection
    [f.IsLocalCompleteIntersection]
    [MonoidalCategory (DerivedCategory (ModuleCat.{u, u} A))]
    (T : DerivedCategory.DerivedTensor.Right.Monoidal.Model (C := ModuleCat.{u, u} A)) :
    MonoidalCategory.isInvertibleObject
      (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R))) := sorry

/-- At every derived module, a presentation-defined upper-shriek functor for a local
complete-intersection homomorphism of Noetherian rings is isomorphic to derived tensoring
with its value on the base ring. -/
theorem objIsomorphicTensorDualOfLocalCompleteIntersection
    [f.IsLocalCompleteIntersection]
    (K : DerivedCategory (ModuleCat.{u, u} R)) :
    IsIsomorphic (p.functor.obj K)
      ((derivedTensorChangeOfRings f
        (p.functor.obj (ModuleCat.single0 (ModuleCat.of R R)))).obj K) := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
