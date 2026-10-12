/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.Finite.Defs
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap67.Lemma_67_49_1_FiniteComponents
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Finite restriction of a generically finite morphism of algebraic spaces

A locally finite type morphism of algebraic spaces onto a decent target, with
finitely many matching codimension-zero points, becomes finite after
restriction to a dense open of the target if it is quasi-compact or separated.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.21.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Assume `f` is locally of finite type. Let `X⁰ ⊂ |X|`
and `Y⁰ ⊂ |Y|` denote the sets of codimension `0` points of `X` and of `Y`.
Assume `Y` is decent, `X⁰` and `Y⁰` are finite and `f⁻¹(Y⁰) = X⁰`, and either
`f` is quasi-compact or `f` is separated. Then there exists a dense open
`V ⊂ Y` such that `f⁻¹(V) ⟶ V` is finite.

Here `|X|` and `|Y|` are `Points X` and `Points Y`, `|f|` is `Points.map f`,
`X⁰` and `Y⁰` are `codimZeroPoints X` and `codimZeroPoints Y`, `V ⊂ Y` is an
`OpenSubspace Y`, dense means `Dense V.pointsSet`, and `f⁻¹(V) ⟶ V` is
`pullback.snd f V.ι`. -/
@[stacks 0BBC]
theorem exists_dense_open_isFinite_restrict_of_preimage_codimZeroPoints_eq
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent Y]
    (hX : (codimZeroPoints X).Finite) (hY : (codimZeroPoints Y).Finite)
    (hpreimage : Points.map f ⁻¹' codimZeroPoints Y = codimZeroPoints X)
    (hqc_or_sep : QuasiCompact f ∨ Separated f) :
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsFinite (pullback.snd f V.ι) :=
  sorry

/-- A locally finite type morphism of algebraic spaces onto a decent target,
with finitely many matching codimension-zero points, is finite over a dense
open of the target when it is quasi-compact. -/
theorem exists_dense_open_isFinite_restrict_of_quasiCompact
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent Y] [QuasiCompact f]
    (hX : (codimZeroPoints X).Finite) (hY : (codimZeroPoints Y).Finite)
    (hpreimage : Points.map f ⁻¹' codimZeroPoints Y = codimZeroPoints X) :
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsFinite (pullback.snd f V.ι) :=
  sorry

/-- A locally finite type morphism of algebraic spaces onto a decent target,
with finitely many matching codimension-zero points, is finite over a dense
open of the target when it is separated. -/
theorem exists_dense_open_isFinite_restrict_of_separated
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent Y] [Separated f]
    (hX : (codimZeroPoints X).Finite) (hY : (codimZeroPoints Y).Finite)
    (hpreimage : Points.map f ⁻¹' codimZeroPoints Y = codimZeroPoints X) :
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsFinite (pullback.snd f V.ι) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
