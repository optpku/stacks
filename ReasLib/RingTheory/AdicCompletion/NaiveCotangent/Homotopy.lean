/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.NaiveCotangent
public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Presentation independence of completed naive cotangent complexes

Finite completed polynomial presentations of an adically complete algebra of
topologically finite type give homotopy-equivalent naive cotangent complexes.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Algebra.NaiveCotangent.Adic

/-- Any two finite completed polynomial presentations of an adically complete
algebra of topologically finite type over a Noetherian ring give homotopy-equivalent
completed naive cotangent complexes. -/
theorem naiveCotangent_homotopyEquiv
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
    {ι ι' : Type u} [Fintype ι] [Fintype ι']
    (P : Presentation A B I ι) (Q : Presentation A B I ι') :
    Nonempty (HomotopyEquiv (naiveCotangent I P) (naiveCotangent I Q)) :=
  sorry

/-- The completed naive cotangent complexes from any two finite completed
polynomial presentations of an adically complete algebra of topologically finite
type over a Noetherian ring are isomorphic in the homotopy category of modules. -/
theorem naiveCotangent_iso
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
    {ι ι' : Type u} [Fintype ι] [Fintype ι']
    (P : Presentation A B I ι) (Q : Presentation A B I ι') :
    Nonempty
      ((HomotopyCategory.quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (naiveCotangent I P) ≅
        (HomotopyCategory.quotient (ModuleCat B) (ComplexShape.down ℕ)).obj
          (naiveCotangent I Q)) :=
  sorry

end Algebra.NaiveCotangent.Adic
