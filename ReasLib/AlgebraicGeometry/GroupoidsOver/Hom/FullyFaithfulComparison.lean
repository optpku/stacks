module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Hom.LimitPreserving

/-!
# Fully faithful Hom-colimit comparison

For a 1-morphism of categories fibred in groupoids, full faithfulness of the
comparison `colim 𝒳_{U_i} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{U_i}` along directed affine
inverse limits is the Hom-colimit pullback field of `Hom.LimitPreserving`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits TypeCat
open CategoryTheory.Functor
open CategoryTheory.Functor.Fiber
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.Groupoids.Hom

open AlgebraicGeometry.Groupoids (homFunctor homCocone)

/-- Full faithfulness of the fibre-category comparison
`colim 𝒳_{U_i} ⟶ 𝒳_U ×_{𝒴_U} colim 𝒴_{U_i}` along every directed inverse
limit of affine schemes over `S`, encoded as pullbacks of fibre Hom-colimits. -/
class FullyFaithfulComparison {S : Scheme.{u}} {X Y : GroupoidsOver S}
    (p : X ⟶ Y) : Prop where
  /-- Fibre Hom-colimit squares along directed affine inverse limits are
  pullbacks. -/
  hom_isPullback : ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
    (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
    ∀ (i : I) (x y : X.p.Fiber (D.obj i))
      [HasColimit (homFunctor x y)]
      [HasColimit (homFunctor ((fiberFunctor p (D.obj i)).obj x)
          ((fiberFunctor p (D.obj i)).obj y))],
      IsPullback (colimit.desc (homFunctor x y) (homCocone c x y))
        (colimMap (fiberHomFunctor p x y)) (fiberHomToLimit p c x y)
        (colimit.desc
          (homFunctor ((fiberFunctor p (D.obj i)).obj x)
            ((fiberFunctor p (D.obj i)).obj y))
          (homCocone c ((fiberFunctor p (D.obj i)).obj x)
            ((fiberFunctor p (D.obj i)).obj y)))

namespace FullyFaithfulComparison

/-- Full faithfulness of the comparison is the Hom-colimit pullback along every
directed affine inverse limit. -/
theorem spec {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y)
    [FullyFaithfulComparison p] {I : Type u} [Preorder I] [Nonempty I]
    [IsDirected I (· ≤ ·)] (D : OrderDual I ⥤ Over S) (c : Cone D)
    (hc : IsLimit c) (hD : ∀ i : I, IsAffine (D.obj i).left)
    (hpt : IsAffine c.pt.left) (i : I) (x y : X.p.Fiber (D.obj i))
    [HasColimit (homFunctor x y)]
    [HasColimit (homFunctor ((fiberFunctor p (D.obj i)).obj x)
        ((fiberFunctor p (D.obj i)).obj y))] :
    IsPullback (colimit.desc (homFunctor x y) (homCocone c x y))
      (colimMap (fiberHomFunctor p x y)) (fiberHomToLimit p c x y)
      (colimit.desc
        (homFunctor ((fiberFunctor p (D.obj i)).obj x)
          ((fiberFunctor p (D.obj i)).obj y))
        (homCocone c ((fiberFunctor p (D.obj i)).obj x)
          ((fiberFunctor p (D.obj i)).obj y))) := sorry

/-- A 1-morphism has fully faithful comparison if and only if every directed
affine inverse limit yields a pullback of fibre Hom-colimits. -/
theorem iff {S : Scheme.{u}} {X Y : GroupoidsOver S} (p : X ⟶ Y) :
    FullyFaithfulComparison p ↔
      ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
        (D : OrderDual I ⥤ Over S) (c : Cone D), IsLimit c →
        (∀ i : I, IsAffine (D.obj i).left) → IsAffine c.pt.left →
        ∀ (i : I) (x y : X.p.Fiber (D.obj i))
          [HasColimit (homFunctor x y)]
          [HasColimit (homFunctor ((fiberFunctor p (D.obj i)).obj x)
              ((fiberFunctor p (D.obj i)).obj y))],
          IsPullback (colimit.desc (homFunctor x y) (homCocone c x y))
            (colimMap (fiberHomFunctor p x y)) (fiberHomToLimit p c x y)
            (colimit.desc
              (homFunctor ((fiberFunctor p (D.obj i)).obj x)
                ((fiberFunctor p (D.obj i)).obj y))
              (homCocone c ((fiberFunctor p (D.obj i)).obj x)
                ((fiberFunctor p (D.obj i)).obj y))) := sorry

/-- A limit-preserving 1-morphism has fully faithful Hom-colimit comparison. -/
instance of_limitPreserving {S : Scheme.{u}} {X Y : GroupoidsOver S}
    {p : X ⟶ Y} [LimitPreserving p] : FullyFaithfulComparison p := sorry

/-- The identity 1-morphism has fully faithful Hom-colimit comparison. -/
instance id {S : Scheme.{u}} {X : GroupoidsOver S} :
    FullyFaithfulComparison (𝟙 X) := sorry

end FullyFaithfulComparison

end AlgebraicGeometry.Groupoids.Hom
