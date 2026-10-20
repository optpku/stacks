/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.UpperShriek
import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Coextension.InvertibleKernel

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.ModuleCat.UpperShriek.Presentation

variable {R A : Type u} [CommRing R] [CommRing A]
  [IsNoetherianRing R] [IsNoetherianRing A]

/-- The upper-shriek functors associated to any two finite polynomial presentations
of a finite-type homomorphism of Noetherian rings are naturally isomorphic. -/
theorem functor_isIsomorphic (f : R →+* A) (hf : f.FiniteType)
    (p q : Presentation f) : IsIsomorphic p.functor q.functor := sorry

/-- Evaluating the upper-shriek functors associated to two finite polynomial
presentations at the same derived module gives isomorphic objects. -/
theorem objIsomorphic (f : R →+* A) (hf : f.FiniteType) (p q : Presentation f)
    (K : DerivedCategory (ModuleCat.{u, u} R)) :
    IsIsomorphic (p.functor.obj K) (q.functor.obj K) := sorry

end CategoryTheory.ModuleCat.UpperShriek.Presentation
