module

public import Mathlib.Data.Finite.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Support
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.FieldPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent

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
  Iff.rfl

/-- If finite families of rational points of `X` lie in affine opens, then any
given finite family is contained in the point-set of an affine open subspace. -/
theorem exists_affineOpen_of_finiteRationalPoints {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    (hX : finiteRationalPointsContainedInAffine X) {ι : Type u} [Finite ι]
    (p : ι → (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ⟶ X)) :
    ∃ U : OpenSubspace X, IsAffine U.X ∧
      Set.range (fun i ↦ fieldPointsToPoints (𝟙 (Spec (CommRingCat.of k))) (p i)) ⊆
        U.pointsSet :=
  hX p

namespace IsScheme

/-- A decent algebraic space locally of finite type over a field is a scheme if
its base change to the algebraic closure is a scheme and every finite family
of rational points of that base change is contained in an affine open. -/
@[stacks 0B88]
theorem of_finiteRationalPoints_affine {k : Type u} [Field k]
    (X : AlgebraicSpace (Spec (CommRingCat.of k)))
    [IsDecent X] [LocallyOfFiniteType (SchemeRealization.toBase X)]
    (h_scheme : IsScheme (baseChange (FieldExtension.specMap k (AlgebraicClosure k)) X))
    (h_affine : finiteRationalPointsContainedInAffine
      (baseChange (FieldExtension.specMap k (AlgebraicClosure k)) X)) :
    IsScheme X :=
  sorry

end IsScheme

end AlgebraicGeometry.AlgebraicSpace
