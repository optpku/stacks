/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.LocalRing.Defs
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Definition_66_4_1_Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PuncturedSpectrum

/-!
# The punctured spectrum as an algebraic space

For a local ring `A`, the scheme `Spec(A)` and its open complement
`U = Spec(A) \ {𝔪}` are algebraic spaces over `Spec(A)`, and the open
immersion `U ⟶ Spec(A)` is the Yoneda image of the scheme-level open
immersion.
-/

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

universe u

#check (AlgebraicGeometry.AlgebraicSpace.specSpace :
  ∀ (A : Type u) [CommRing A], AlgebraicSpace (Spec (CommRingCat.of A)))

#check (AlgebraicGeometry.AlgebraicSpace.specSpace_eq :
  ∀ (A : Type u) [CommRing A],
    specSpace A = ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A)))))

#check (AlgebraicGeometry.AlgebraicSpace.puncturedSpace :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    AlgebraicSpace (Spec (CommRingCat.of A)))

#check (AlgebraicGeometry.AlgebraicSpace.puncturedSpace_eq :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    puncturedSpace A = ofOver (Over.mk (PuncturedSpectrum.puncturedOpen A).ι))

#check (AlgebraicGeometry.AlgebraicSpace.puncturedι :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A], puncturedSpace A ⟶ specSpace A)

#check (AlgebraicGeometry.AlgebraicSpace.puncturedι_eq :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A],
    puncturedι A =
      ofOverMap
        (Over.homMk (PuncturedSpectrum.puncturedOpen A).ι
          (Category.comp_id (PuncturedSpectrum.puncturedOpen A).ι)))

#check (AlgebraicGeometry.AlgebraicSpace.instIsOpenImmersion_puncturedι :
  ∀ (A : Type u) [CommRing A] [IsLocalRing A], IsOpenImmersion (puncturedι A))
