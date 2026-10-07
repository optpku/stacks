module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Yoneda
public import stacks_project.Chap98.Definition_98_22_1_DeformationSituation
public import stacks_project.Chap98.Lemma_98_25_2
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 98.25.4

A limit-preserving sheaf transformation on `(Sch/S)_τ` is representable if and
only if its restriction to `(Noetherian/S)_τ` is representable, and if and only
if this can be tested on affine finite type objects mapping into an affine open
of `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry.Scheme.Hom
open AlgebraicGeometry.Scheme.Over

universe u

namespace AlgebraicGeometry.StandardTopology

/-- Relative representability of a natural transformation of functors on the
locally Noetherian site, tested only on affine objects of finite type over `S`
that map into an affine open of `S`. -/
def relativelyRepresentableOnAffineFiniteType {S : Scheme.{u}}
    {F G : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (a : F ⟶ G) : Prop :=
  ∀ (V : (locallyNoetherian S).FullSubcategory) [IsAffine V.obj.left]
    [LocallyOfFiniteType V.obj.hom],
    MapsIntoAffineOpen V.obj.hom →
      ∀ (ξ : uliftYoneda.{u + 1}.obj V ⟶ G),
        ∃ (W : (locallyNoetherian S).FullSubcategory) (p : W ⟶ V)
          (q : uliftYoneda.{u + 1}.obj W ⟶ F),
          IsPullback q (uliftYoneda.{u + 1}.map p) a ξ

/-- Unfolding of `relativelyRepresentableOnAffineFiniteType` into the truncated
Yoneda-relative pullback quantification. -/
theorem relativelyRepresentableOnAffineFiniteType_iff {S : Scheme.{u}}
    {F G : (locallyNoetherian S).FullSubcategoryᵒᵖ ⥤ Type (u + 1)}
    (a : F ⟶ G) :
    relativelyRepresentableOnAffineFiniteType a ↔
      ∀ (V : (locallyNoetherian S).FullSubcategory) [IsAffine V.obj.left]
        [LocallyOfFiniteType V.obj.hom],
        MapsIntoAffineOpen V.obj.hom →
          ∀ (ξ : uliftYoneda.{u + 1}.obj V ⟶ G),
            ∃ (W : (locallyNoetherian S).FullSubcategory) (p : W ⟶ V)
              (q : uliftYoneda.{u + 1}.obj W ⟶ F),
              IsPullback q (uliftYoneda.{u + 1}.map p) a ξ := sorry

/-- Lemma 98.25.4 (1): let `τ` be Zariski, étale, smooth, syntomic, or fppf, let
`S` be locally Noetherian, and let `F', G' : (Over S)ᵒᵖ ⥤ Type (u + 1)` be
limit-preserving sheaves. A transformation `a' : F' ⟶ G'` is representable as a
transformation of functors, in the sense of `uliftYoneda.relativelyRepresentable`
rather than `HasPullbacksAlong`, if and only if its restriction
`(restrictPresheaf S).map a'` to `(Noetherian/S)_τ` is representable. -/
@[stacks 0GE5]
theorem relativelyRepresentable_restrict_iff (τ : StandardTopology)
    {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (u + 1)}
    (hF' : isLimitPreservingSheaf τ S F') (hG' : isLimitPreservingSheaf τ S G')
    (a' : F' ⟶ G') :
    uliftYoneda.{u + 1}.relativelyRepresentable a' ↔
      uliftYoneda.{u + 1}.relativelyRepresentable ((restrictPresheaf S).map a') :=
  sorry

/-- Lemma 98.25.4 (2): in the same setting, the restriction of `a'` is
representable on `(Noetherian/S)_τ` if and only if for every affine finite type
object `V` of that site mapping into an affine open of `S`, and every map
`ξ : uliftYoneda.obj V ⟶ G`, the fibre product functor `F ×_G V` is representable. -/
@[stacks 0GE5]
theorem relativelyRepresentable_restrict_iff_affineFiniteType
    (τ : StandardTopology) {S : Scheme.{u}} [IsLocallyNoetherian S]
    {F' G' : (Over S)ᵒᵖ ⥤ Type (u + 1)}
    (hF' : isLimitPreservingSheaf τ S F') (hG' : isLimitPreservingSheaf τ S G')
    (a' : F' ⟶ G') :
    uliftYoneda.{u + 1}.relativelyRepresentable ((restrictPresheaf S).map a') ↔
      relativelyRepresentableOnAffineFiniteType ((restrictPresheaf S).map a') :=
  sorry

end AlgebraicGeometry.StandardTopology
