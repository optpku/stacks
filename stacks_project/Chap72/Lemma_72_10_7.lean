module

public import Mathlib.Data.Finite.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Lemma_65_16_1_ChangeOfBase
public import stacks_project.Chap66.Lemma_66_13_1_IsScheme
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap67.Definition_67_20_2_Affine
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Lemma_67_24_2_FieldPoints
public import stacks_project.Chap68.Lemma_68_12_8_Decent

/-!
# Schemes from affine covers of rational points after algebraic closure

A decent algebraic space locally of finite type over a field is a scheme if its
base change to the algebraic closure is a scheme whose finite sets of rational
points lie in affine opens.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CommRingCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Finite families of `k`-rational points of an algebraic space over a field `k`
are contained in a single affine open subspace. -/
def finiteRationalPointsContainedInAffine {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) : Prop :=
  ∀ {ι : Type u} [Finite ι]
    (p : ι → (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⟶ X)),
    ∃ U : OpenSubspace X, IsAffine U.X ∧
      Set.range (fun i ↦ fieldPointsToPoints (𝟙 (Spec (CommRingCat.of k))) (p i)) ⊆
        U.pointsSet

/-- Finite families of `k`-rational points lie in an affine open if and only if
each such family is contained in the point-set of an affine open subspace. -/
theorem finiteRationalPointsContainedInAffine_iff {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k))) :
    finiteRationalPointsContainedInAffine X ↔
      ∀ {ι : Type u} [Finite ι]
        (p : ι → (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⟶ X)),
        ∃ U : OpenSubspace X, IsAffine U.X ∧
          Set.range (fun i ↦ fieldPointsToPoints (𝟙 (Spec (CommRingCat.of k))) (p i)) ⊆
            U.pointsSet :=
  sorry

/-- A finite family of `k`-rational points of `X` is contained in the point-set of
an affine open subspace. -/
theorem exists_affineOpen_of_finiteRationalPoints {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hX : finiteRationalPointsContainedInAffine X) {ι : Type u} [Finite ι]
    (p : ι → (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⟶ X)) :
    ∃ U : OpenSubspace X, IsAffine U.X ∧
      Set.range (fun i ↦ fieldPointsToPoints (𝟙 (Spec (CommRingCat.of k))) (p i)) ⊆
        U.pointsSet :=
  sorry

namespace IsScheme

/-- Lemma 72.10.7: Let `k` be a field with algebraic closure `AlgebraicClosure k`.
Let `X` be an algebraic space over `k` such that `X` is decent and locally of
finite type over `k`, the base change of `X` along
`FieldExtension.specMap k (AlgebraicClosure k)` is a scheme, and any finite set
of `AlgebraicClosure k`-rational points of that base change is contained in an
affine open. Then `X` is a scheme. -/
@[stacks 0B88]
theorem of_finiteRationalPoints_affine {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [IsDecent X] [LocallyOfFiniteType (toBase X)]
    (h_scheme : IsScheme (baseChange (FieldExtension.specMap k (AlgebraicClosure k)) X))
    (h_affine : finiteRationalPointsContainedInAffine
      (baseChange (FieldExtension.specMap k (AlgebraicClosure k)) X)) :
    IsScheme X :=
  sorry

end IsScheme

end AlgebraicGeometry.AlgebraicSpace
