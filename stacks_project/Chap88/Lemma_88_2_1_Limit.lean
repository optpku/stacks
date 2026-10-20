/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType.InverseLimit

/-!
# Inverse-limit reconstruction comparisons

The inverse-limit functor and its unit and counit comparisons are available
from the canonical inverse-limit owner.
-/

@[expose] public section

open CategoryTheory

universe u

variable {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)

#check (AdicAlgebraSystem.limitFunctor I hI :
  AdicAlgebraSystem A I ⥤ CommAlgCat.TopologicallyFiniteType.{u} A I)

#check (AdicAlgebraSystem.limitFunctorUnitIso I hI :
  𝟭 (CommAlgCat.TopologicallyFiniteType.{u} A I) ≅
    CommAlgCat.TopologicallyFiniteType.toAdicSystem I ⋙ AdicAlgebraSystem.limitFunctor I hI)

#check (AdicAlgebraSystem.limitFunctorCounitIso I hI :
  AdicAlgebraSystem.limitFunctor I hI ⋙ CommAlgCat.TopologicallyFiniteType.toAdicSystem I ≅
    𝟭 (AdicAlgebraSystem A I))
