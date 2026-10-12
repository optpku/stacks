/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.JacobsonSpace
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField.Extension
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap67.Definition_67_45_2_Integral
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Finite residue-field extensions give finite morphisms into decent spaces

On a decent algebraic space, a field-valued point over a closed point of the
base with finite residue-field extension is a finite morphism; it is a closed
immersion when the canonical residue-field map is bijective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Scheme.Hom

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 68.14.5 (1): Let `S` be a scheme and `X` a decent algebraic space over `S`.
Given a commutative diagram `Spec(k) ⟶ X` over `S`, if the image `s` of
`Spec(k) ⟶ S` is a closed point and `k / κ(s)` is finite, then
`Spec(k) ⟶ X` is a finite morphism. -/
@[stacks 08AL]
theorem isFinite_of_finite_residueField {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (p : FieldValuedPoint X)
    (hs : closedPointImage p.structureHom ∈ closedPoints S)
    (hfin : Module.Finite (S.residueField (closedPointImage p.structureHom)) p.K) :
    IsFinite p.hom :=
  sorry

/-- Lemma 68.14.5 (2): Let `S` be a scheme and `X` a decent algebraic space over `S`.
Given a commutative diagram `Spec(k) ⟶ X` over `S`, if the image `s` of
`Spec(k) ⟶ S` is a closed point and the canonical map `κ(s) → k` is bijective,
then `Spec(k) ⟶ X` is a closed immersion. -/
@[stacks 08AL]
theorem isClosedImmersion_of_eq_residueField {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] (p : FieldValuedPoint X)
    (hs : closedPointImage p.structureHom ∈ closedPoints S)
    (heq : Function.Bijective
      (algebraMap (S.residueField (closedPointImage p.structureHom)) p.K)) :
    IsClosedImmersion p.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
