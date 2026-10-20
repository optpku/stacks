/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.AdicCompletion.TopologicallyFiniteType.Noetherian
public import ReasLib.Algebra.Category.CommAlgCat.TopologicallyFiniteType

/-!
# Completion and quotient objects over Noetherian rings

Adic completions of finite type algebras and ideal quotients of topologically
finite type algebras give explicit objects of the topologically finite type category.
-/

@[expose] public section

noncomputable section

universe u

namespace CommAlgCat.TopologicallyFiniteType

/-- The adic completion of a finite type algebra over a Noetherian ring, bundled
as a topologically finite type algebra. -/
def ofFiniteType {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    TopologicallyFiniteType.{u} A I :=
  of A I (AdicCompletion (I.map (algebraMap A C)) C)

/-- The underlying algebra of the bundled finite type completion is the adic completion. -/
theorem ofFiniteType_obj {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C] :
    (ofFiniteType I C).obj =
      CommAlgCat.of A (AdicCompletion (I.map (algebraMap A C)) C) :=
  rfl

/-- The quotient of a topologically finite type algebra over a Noetherian ring,
bundled as a topologically finite type algebra. -/
def quotient {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : TopologicallyFiniteType.{u} A I) (J : Ideal B) :
    TopologicallyFiniteType.{u} A I :=
  of A I (B ⧸ J)

/-- The underlying algebra of the bundled quotient is the quotient ring. -/
theorem quotient_obj {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (B : TopologicallyFiniteType.{u} A I) (J : Ideal B) :
    (quotient I B J).obj = CommAlgCat.of A (B ⧸ J) :=
  rfl

end CommAlgCat.TopologicallyFiniteType
