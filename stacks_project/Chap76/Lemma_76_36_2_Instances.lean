/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Affine and decent instances for relative normalization

An affine algebraic space is decent, so it has residue fields. The relative
normalization of a qcqs morphism into an affine algebraic space is itself
affine, hence likewise decent.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An affine algebraic space is decent. -/
instance instIsDecent_of_isAffine {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsAffine X] : IsDecent X :=
  sorry

namespace Hom

/-- The relative normalization of a quasi-compact quasi-separated morphism into
an affine algebraic space is affine. -/
instance instIsAffine_normalization {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [IsAffine Y] :
    IsAffine (normalization f) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
