/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair

/-!
# Separated étale morphisms from a separated scheme

An étale morphism from a separated scheme to an algebraic space is separated in the
sense of Definition 65.5.1, and the represented kernel pair is a separated scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}

/-- Lemma 66.6.4 (1): let `S` be a scheme, `X` an algebraic space over `S`, and `U` a
separated scheme. If `φ : ofOver U ⟶ X` is étale, then `φ` is separated in the sense of
Definition 65.5.1. -/
@[stacks 03FZ]
theorem isSeparated_of_etale [Scheme.IsSeparated U.left] (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@Etale)).presheaf φ) :
    (MorphismProperty.over (@AlgebraicGeometry.IsSeparated :
        MorphismProperty Scheme.{u})).presheaf φ :=
  sorry

/-- Lemma 66.6.4 (2): let `S` be a scheme, `X` an algebraic space over `S`, and `U` a
separated scheme. If `φ : ofOver U ⟶ X` is étale, then the kernel pair
`R = U ×_X U` is a separated scheme. -/
@[stacks 03FZ, instance]
instance isSeparated_kernelPair [Scheme.IsSeparated U.left] (φ : ofOver U ⟶ X)
    (hφ : (MorphismProperty.over (@Etale)).presheaf φ) :
    Scheme.IsSeparated (kernelPair φ hφ.rep).left.left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
