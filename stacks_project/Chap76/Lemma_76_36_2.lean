/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_40_1_FiniteType
public import stacks_project.Chap67.Definition_67_48_3_Normalization
public import stacks_project.Chap67.Lemma_67_9_7
public import stacks_project.Chap68.Definition_68_11_2_ResidueField
public import stacks_project.Chap76.Lemma_76_36_2_Instances
public import stacks_project.Chap76.Lemma_76_36_2_PointsOver

/-!
# Finite fibres of relative Stein normalization

For a universally closed quasi-separated morphism of algebraic spaces which is
locally of finite type and has affine target, the relative-normalization
morphism has finite point-set fibres, and each residue-field extension of a
point of such a fibre is finite.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- Lemma 76.36.2 (1): In the Stein factorization of a universally closed
quasi-separated morphism `f : X ⟶ Y` of algebraic spaces, if `f` is locally of
finite type and `Y` is affine, then for every point `y` of `Y` the fibre
`(fromNormalization f).pointsOver y` is finite. -/
@[stacks 0E1C]
theorem fromNormalization_fiberFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [UniversallyClosed f] [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAffine Y] (y : Points Y) :
    Set.Finite (pointsOver (fromNormalization f) y) :=
  sorry

/-- Lemma 76.36.2 (2): In the same setting, each residue-field extension
`κ(yᵢ) / κ(y)` along a point of the fibre of `fromNormalization f` is finite. -/
@[stacks 0E1C]
instance instModuleFiniteResidueFieldFromNormalization
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [UniversallyClosed f] [QuasiSeparated f] [LocallyOfFiniteType f]
    [IsAffine Y] (y : Points Y) (y' : pointsOver (fromNormalization f) y) :
    Module.Finite (Y.residueField y) ((normalization f).residueField y') :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
