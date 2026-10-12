/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Module.Support
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap67.Lemma_67_15_1_ModuleSupport
public import stacks_project.Chap68.Lemma_68_12_8_Decent
public import stacks_project.Chap69.Lemma_69_12_2_Coherent
public import stacks_project.Chap82.Lemma_82_4_4_GenericPoint
public import stacks_project.Chap82.Lemma_82_4_4_Length

/-!
# Finite nonzero length at a point of a coherent module on a locally Noetherian algebraic space

On a locally Noetherian algebraic space, finite nonzero length of a coherent module at a point
is equivalent to the existence, and to the universality, of an étale scheme chart on which the
point is a generic point of an irreducible component of the support. If the space is decent,
this is also equivalent to the same condition on `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]

/-- Lemma 82.4.4 (1): Let `S` be a scheme and let `X` be a locally Noetherian algebraic space
over `S`. Let `F` be a coherent `𝒪_X`-module. Let `x ∈ |X|`. The following are equivalent:
there exists an étale morphism `φ : ofOver U ⟶ X` from a scheme and a point `u : U.left`
mapping to `x` which is a generic point of an irreducible component of
`Scheme.Modules.moduleSupport (etaleSchemeModule φ F)`; this holds for every such étale chart
and point over `x`; and `hasFiniteNonzeroLengthAt F x`. -/
@[stacks 0EE4]
theorem hasFiniteNonzeroLengthAt_tfae (F : X.Modules) [F.IsCoherent] (x : Points X) :
    List.TFAE
      [∃ (U : Over S) (φ : ofOver U ⟶ X),
          Etale φ ∧ ∃ u : U.left,
            Points.mapOfOver φ u = x ∧
              IsGenericPoint.ofIrreducibleComponent u
                (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
          Points.mapOfOver φ u = x →
            IsGenericPoint.ofIrreducibleComponent u
              (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        hasFiniteNonzeroLengthAt F x] :=
  sorry

/-- Lemma 82.4.4 (2): Let `S` be a scheme and let `X` be a locally Noetherian algebraic space
over `S`. Let `F` be a coherent `𝒪_X`-module. Let `x ∈ |X|`. If `X` is decent, then the three
conditions of `hasFiniteNonzeroLengthAt_tfae` are also equivalent to `x` being a generic point
of an irreducible component of `moduleSupport F`. In this locally Noetherian setting, decent is
equivalent to (absolutely) quasi-separated, by
`IsAbsolutelyQuasiSeparated.of_isLocallyNoetherian_isDecent` and
`instIsDecent_of_isQuasiSeparated`. -/
@[stacks 0EE4]
theorem hasFiniteNonzeroLengthAt_tfae_of_isDecent [IsDecent X] (F : X.Modules) [F.IsCoherent]
    (x : Points X) :
    List.TFAE
      [∃ (U : Over S) (φ : ofOver U ⟶ X),
          Etale φ ∧ ∃ u : U.left,
            Points.mapOfOver φ u = x ∧
              IsGenericPoint.ofIrreducibleComponent u
                (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        ∀ (U : Over S) (φ : ofOver U ⟶ X) [Etale φ] (u : U.left),
          Points.mapOfOver φ u = x →
            IsGenericPoint.ofIrreducibleComponent u
              (Scheme.Modules.moduleSupport (etaleSchemeModule φ F)),
        hasFiniteNonzeroLengthAt F x,
        IsGenericPoint.ofIrreducibleComponent x (moduleSupport F)] :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
