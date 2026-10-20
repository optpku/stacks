/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Classifying.MultiplicativeGroup
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Dimension.QuasiDM
public import ReasLib.AlgebraicGeometry.AlgebraicStack.SchemeTheoreticImage.Dimension
import StacksCheckRecall

/-!
# Negative fibre dimension versus quasi-DM image inequalities

The inequality `dimension Z ≤ dimension T` for scheme-theoretic images need not
hold without a quasi-DM hypothesis, because fibres of morphisms of algebraic
stacks may have negative dimension, as for `[Spec k / 𝔾ₘ] ⟶ Spec k`. Quasi-DM
morphisms have non-negative fibre dimension, and then the image inequality
holds; Lemma 107.5.24 is the more general result.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped AlgebraicGeometry Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Remark 107.5.23 (1): in the context of the preceding lemma it need not be
that `dimension T ≥ dimension Z`, because fibres of `f` are algebraic stacks and
may have negative dimension. This is illustrated by the structure morphism
`baseProjection (classifying (𝔾ₘ[Spec (.of k)]).toGrp)`, i.e.
`[Spec k / 𝔾ₘ] ⟶ Spec k`. -/
@[stacks 0DS5] #check
  (AlgebraicGeometry.AlgebraicStack.dimension_classifying_multiplicativeGroup_lt_dimension_spec :
    ∀ (k : Type u) [Field k],
      dimension (classifying (𝔾ₘ[Spec (.of k)]).toGrp) <
        dimension (GroupoidsOver.slice (Over.mk (𝟙 (Spec (.of k))))))

/- The classifying stack `[Spec k / 𝔾ₘ]` has dimension `-1`. -/
#check (AlgebraicGeometry.AlgebraicStack.dimension_classifying_multiplicativeGroup :
  ∀ (k : Type u) [Field k],
    dimension (classifying (𝔾ₘ[Spec (.of k)]).toGrp) = ((-1 : ℤ) : EInt))

/- A locally Noetherian quasi-DM algebraic stack has non-negative local dimension. -/
#check (AlgebraicGeometry.AlgebraicStack.dimensionAt_nonneg_of_quasiDM :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
    [IsLocallyNoetherian X] [QuasiDM (baseProjection.{u + 1, u, u + 1} X)]
    (x : Points X), (0 : EInt) ≤ dimensionAt x)

/- Remark 107.5.23 (2): if `f` is quasi-DM in the sense of Morphisms of Stacks,
Definition 101.4.1, then the fibres over points of the target are quasi-DM
algebraic stacks, and hence are of non-negative dimension. -/
@[stacks 0DS5] #check
  (AlgebraicGeometry.AlgebraicStack.dimension_nonneg_of_quasiDM :
    ∀ {S : Scheme.{u}} {X : GroupoidsOver S} [AlgebraicStack X]
      [IsLocallyNoetherian X] [Nonempty (Points X)]
      [QuasiDM (baseProjection.{u + 1, u, u + 1} X)],
      (0 : EInt) ≤ dimension X)

/- Remark 107.5.23 (3): a locally of finite type quasi-DM morphism of locally
Noetherian algebraic stacks has non-negative relative dimension at every point,
so its fibres cannot contribute a negative correction to dimension. -/
@[stacks 0DS5] #check
  (AlgebraicGeometry.AlgebraicStack.relativeDimensionAt_nonneg_of_quasiDM :
    ∀ {S : Scheme.{u}} {T X : GroupoidsOver S}
      [AlgebraicStack T] [AlgebraicStack X]
      [IsLocallyNoetherian T] [IsLocallyNoetherian X]
      {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f] (t : Points T),
      (0 : EInt) ≤ relativeDimensionAt f t)

/- Remark 107.5.23 (4): morphisms that are representable by algebraic spaces are
quasi-DM. -/
@[stacks 0DS5] #check
  (AlgebraicGeometry.AlgebraicStack.DM.of_relativelyRepresentableByAlgebraicSpaces :
    ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
      [AlgebraicStack X] [AlgebraicStack Y] {f : X ⟶ Y},
      relativelyRepresentableByAlgebraicSpaces f → DM f)

#check (AlgebraicGeometry.AlgebraicStack.QuasiDM.of_DM :
  ∀ {S : Scheme.{u}} {X Y : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) [DM f], QuasiDM f)

/- Remark 107.5.23 (5): in this case the lemma implies `dimension Z ≤ dimension T`;
in fact the following more general result. -/
@[stacks 0DS5] #check (AlgebraicGeometry.AlgebraicStack.dimension_schemeTheoreticImage_le :
  ∀ {S : Scheme.{u}} {T X Z : GroupoidsOver S}
    [AlgebraicStack T] [AlgebraicStack X] [AlgebraicStack Z]
    [IsLocallyNoetherian T] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]
    [IsJacobson T] [IsJacobson X] [IsPseudoCatenary T] [IsPseudoCatenary X]
    [IsIrreducible T] {f : T ⟶ X} [LocallyOfFiniteType f] [QuasiDM f]
    [IsQuasiSeparated X]
    {toImage : T ⟶ Z} {ι : Z ⟶ X} [IsSchemeTheoreticImage f toImage ι],
    dimension Z ≤ dimension T)

end AlgebraicGeometry.AlgebraicStack
