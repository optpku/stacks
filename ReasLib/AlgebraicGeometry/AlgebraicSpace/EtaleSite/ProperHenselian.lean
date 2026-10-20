/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Sections
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SpecialFiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import Mathlib.RingTheory.Henselian

/-!
# Small étale global sections over henselian pairs

For a proper algebraic space over a henselian pair, restriction to the special
fibre induces a bijection on global sections of every sheaf of sets.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
open scoped MorphismOfTopoiIn

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- For an algebraic space proper over a henselian pair `(A, I)`, restriction
to the special fibre `X ×_{Spec A} Spec(A / I)` induces a bijection on global
sections of every sheaf of sets on the small étale site. -/
theorem smallEtaleGlobalSections_bijective_of_properHenselianPair
    {A : Type u} [CommRing A] (I : Ideal A) [HenselianRing A I]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Proper (SchemeRealization.toBase X)]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Function.Bijective
      (smallEtaleGlobalSectionsPullback
        (pullback.fst (SchemeRealization.toBase X) (specQuotientι I)) F) :=
  sorry

/-- For an algebraic space proper over a henselian local ring, restriction to
the closed fibre induces a bijection on global sections of every sheaf of sets
on the small étale site. -/
theorem smallEtaleGlobalSections_bijective_of_properHenselianLocal
    {A : Type u} [CommRing A] [HenselianLocalRing A]
    {X : AlgebraicSpace (Spec (CommRingCat.of A))}
    [Proper (SchemeRealization.toBase X)]
    (F : Sheaf (smallEtaleTopology X) (Type (u + 1))) :
    Function.Bijective
      (smallEtaleGlobalSectionsPullback
        (pullback.fst (SchemeRealization.toBase X)
          (specQuotientι (IsLocalRing.maximalIdeal A))) F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
