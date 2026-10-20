/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_18_1_Dominant
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_27_6_LocallyQuasiFinite
public import stacks_project.Chap67.Lemma_67_33_3_ResidueFieldTrdeg
public import stacks_project.Chap68.Definition_68_22_1_GenericPoints
public import stacks_project.Chap72.Definition_72_4_1_Integral
public import stacks_project.Chap76.Lemma_76_36_2_PointsOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints.Dominant
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GenericallyFinite.Integral
import StacksCheckRecall

/-!
# Generically finite morphisms of integral algebraic spaces

A dominant locally finite type morphism of integral algebraic spaces is
generically finite in several equivalent senses: residue-field transcendence
degree zero, a finite residue-field extension at the generic point, a finite
restriction between nonempty affine opens, quasi-finiteness at the generic
point, and a singleton generic fibre. If the morphism is quasi-compact or
separated, this is also equivalent to finiteness over a nonempty affine open
of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 72.5.1 (1) -/
@[stacks 0AD5] #check
  (AlgebraicGeometry.AlgebraicSpace.genericallyFinite_tfae :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, [IsIntegral X] → [IsIntegral Y] →
      (f : X ⟶ Y) → [LocallyOfFiniteType f] → [Dominant f] → {x : Points X} →
      x ∈ genericPoints X →
      List.TFAE
        [ residueFieldTrdegAt f x = 0
        , FiniteDimensional (Y.residueField (Points.map f x)) (X.residueField x)
        , ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (g : U.X ⟶ V.X),
            U.pointsSet.Nonempty ∧ V.pointsSet.Nonempty ∧ IsAffine U.X ∧
              IsAffine V.X ∧ g ≫ V.ι = U.ι ≫ f ∧ IsFinite g
        , QuasiFiniteAt f x
        , Points.map f ⁻¹' {Points.map f x} = {x} ])

/- Lemma 72.5.1 (2) -/
@[stacks 0AD5] #check
  (AlgebraicGeometry.AlgebraicSpace.genericallyFinite_tfae_of_quasiCompact_or_separated :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, [IsIntegral X] → [IsIntegral Y] →
      (f : X ⟶ Y) → [LocallyOfFiniteType f] → [Dominant f] → {x : Points X} →
      x ∈ genericPoints X → (QuasiCompact f ∨ Separated f) →
      List.TFAE
        [ residueFieldTrdegAt f x = 0
        , FiniteDimensional (Y.residueField (Points.map f x)) (X.residueField x)
        , ∃ (U : OpenSubspace X) (V : OpenSubspace Y) (g : U.X ⟶ V.X),
            U.pointsSet.Nonempty ∧ V.pointsSet.Nonempty ∧ IsAffine U.X ∧
              IsAffine V.X ∧ g ≫ V.ι = U.ι ≫ f ∧ IsFinite g
        , QuasiFiniteAt f x
        , Points.map f ⁻¹' {Points.map f x} = {x}
        , ∃ V : OpenSubspace Y,
            V.pointsSet.Nonempty ∧ IsAffine V.X ∧
              IsFinite (pullback.snd f V.ι) ])

#check
  (AlgebraicGeometry.AlgebraicSpace.map_mem_genericPoints_of_isDominant :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, [IsDecent X] → [IsDecent Y] →
      [IsIrreducible X] → [IsIrreducible Y] → (f : X ⟶ Y) → [Dominant f] →
      {x : Points X} → x ∈ genericPoints X → Points.map f x ∈ genericPoints Y)

end AlgebraicGeometry.AlgebraicSpace
