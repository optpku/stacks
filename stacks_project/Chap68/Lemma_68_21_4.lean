/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GenericallyFinite
import StacksCheckRecall

/-!
# Finite restriction of a generically finite morphism of algebraic spaces

A locally finite type morphism of algebraic spaces to a decent target, with
finitely many matching codimension-zero points, becomes finite after
restriction to a dense open of the target if it is quasi-compact or separated.
-/

@[expose]
public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.21.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
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
#check (AlgebraicGeometry.AlgebraicSpace.exists_dense_open_isFinite_restrict_of_preimage_codimZeroPoints_eq :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [IsDecent Y]
    (hX : (codimZeroPoints X).Finite) (hY : (codimZeroPoints Y).Finite)
    (hpreimage : Points.map f ⁻¹' codimZeroPoints Y = codimZeroPoints X)
    (hqc_or_sep : QuasiCompact f ∨ Separated f),
    ∃ V : OpenSubspace Y, Dense V.pointsSet ∧ IsFinite (pullback.snd f V.ι))

end AlgebraicGeometry.AlgebraicSpace
