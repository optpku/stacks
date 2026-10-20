/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_26_1_Nagata
public import stacks_project.Chap67.Lemma_67_48_6_Reduced

/-!
# Finiteness of relative normalizations over Nagata algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The relative normalization of a reduced quasi-separated finite-type morphism of
algebraic spaces into a Nagata algebraic space is finite. -/
theorem isFinite_fromNormalization_of_isNagata_of_finiteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsNagata Y] [IsReduced X] :
    IsFinite (fromNormalization f) :=
  sorry

/-- Lemma 67.48.11: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. If `Y` is Nagata, `f` is quasi-separated of finite type,
and `X` is reduced, then the relative normalization `ν : Y' ⟶ Y` of `Y` in `X`,
namely `fromNormalization f : normalization f ⟶ Y`, is finite. -/
@[stacks 0BB0]
instance instIsFiniteFromNormalizationOfIsNagataFiniteType
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [FiniteType f] [QuasiSeparated f] [IsNagata Y] [IsReduced X] :
    IsFinite (fromNormalization f) :=
  isFinite_fromNormalization_of_isNagata_of_finiteType f

end Hom

end AlgebraicGeometry.AlgebraicSpace
