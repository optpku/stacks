/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.HenselianLocalRing.Spectrum

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Stalk.Henselization
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap68.Lemma_68_11_4
public import stacks_project.Chap68.Lemma_68_14_6

/-!
# Henselization of a decent algebraic space at a point

A Type-u henselization of the stalk at an affine elementary étale neighbourhood
realizes `Spec(𝒪_{X,x}^h)` as an algebraic space over `S`, together with the
open complement of a closed point and the punctured henselization.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.henselization_open_le :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S) [IsDecent X]
    {x : Points X} (hx : x ∈ closedPoints (Points X)) (N : EtaleNeighborhood X x)
    (hN : IsAffine N.scheme ∧ Points.mapOfOver N.hom ⁻¹' {x} = {N.point} ∧ N.IsElementary)
    (R : Type u) [CommRing R] [Algebra (N.scheme.presheaf.stalk N.point) R]
    [IsHenselizationOf (N.scheme.presheaf.stalk N.point) R],
    ∃ φ : henselizationPunctured X x N hN R ⟶
        openInverseImage (fromHenselization X x N hN R) (closedPointComplementι X hx),
      φ ≫ openInverseImageι (fromHenselization X x N hN R) (closedPointComplementι X hx) =
        henselizationPuncturedι X x N hN R)

end AlgebraicGeometry.AlgebraicSpace
