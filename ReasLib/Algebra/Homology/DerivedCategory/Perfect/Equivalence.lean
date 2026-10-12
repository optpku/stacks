/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import ReasLib.Algebra.Category.ModuleCat.Finite
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Generation
public import ReasLib.Algebra.Homology.DerivedCategory.TensorProduct
public import ReasLib.CategoryTheory.DerivedCategory.Bounded.CohomologyIn
public import ReasLib.CategoryTheory.DerivedCategory.CohomologyIn.Bounded
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-!
# Linear Equivalences and the Regular Derived Object

This file relates the degree-zero regular module in the bounded derived category of finitely
generated modules to tensor-invertible objects in the ambient derived category.
-/

@[expose] public section

noncomputable section

open CategoryTheory.MonoidalCategory
open scoped DerivedCategory.CohomologyIn

universe u

namespace CategoryTheory.DerivedCategory.Bounded.CohomologyIn

/-- The regular module placed in degree zero in the bounded derived category with finitely
generated cohomology. -/
noncomputable def ringSingle (A : Type u) [CommRing A] :
    Dᵇ[ModuleCat.isFG A] :=
  (Single.functor (ModuleCat.isFG A)).obj (FGModuleCat.of A A)

/-- The ambient image of the bounded regular object is the degree-zero regular module. -/
theorem ambient_ringSingle (A : Type u) [CommRing A] :
    (ambient (ModuleCat.isFG A)).obj (ringSingle A) = ModuleCat.ringSingle A := sorry

end CategoryTheory.DerivedCategory.Bounded.CohomologyIn

namespace CategoryTheory.DerivedCategory

/-- Fixed-right derived tensoring by the ambient image of the regular object under a linear
self-equivalence of the bounded derived category is an equivalence. -/
theorem derivedTensorImageRegular_isEquivalence
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (F : Dᵇ[ModuleCat.isFG A] ⥤ Dᵇ[ModuleCat.isFG A])
    [Functor.Linear A F] [F.IsEquivalence] :
    (derivedTensorProduct
      ((Bounded.CohomologyIn.ambient (ModuleCat.isFG A)).obj
        (F.obj (Bounded.CohomologyIn.ringSingle A)))).IsEquivalence := sorry

/-- A linear self-equivalence of the bounded derived category of finitely generated modules
sends the regular object to a tensor-invertible object in the ambient derived category. -/
theorem isInvertibleObject_image_regular
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (F : Dᵇ[ModuleCat.isFG A] ⥤ Dᵇ[ModuleCat.isFG A])
    [Functor.Linear A F] [F.IsEquivalence]
    [MonoidalCategory (DerivedCategory (ModuleCat A))]
    (T : @DerivedTensor.Right.Monoidal.Model (ModuleCat A) _ _ _ _ _ _ _) :
    isInvertibleObject
      ((Bounded.CohomologyIn.ambient (ModuleCat.isFG A)).obj
        (F.obj (Bounded.CohomologyIn.ringSingle A))) := sorry

end CategoryTheory.DerivedCategory
