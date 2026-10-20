/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.Transitivity
public import ReasLib.RingTheory.CotangentComplex.DirectLimit

@[expose] public section

open CategoryTheory CategoryTheory.Pretriangulated

universe u

namespace Algebra.CotangentComplex

/-- The object of `Under (CommRingCat.of A)` associated to an `A`-algebra `B`. -/
abbrev under (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Under (CommRingCat.of A) :=
  Under.mk (CommRingCat.ofHom (algebraMap A B))

end Algebra.CotangentComplex

#check (Algebra.CotangentComplex.transitivityTriangle :
  ∀ (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C],
    Triangle (DerivedCategory (ModuleCat.{u} C)))
