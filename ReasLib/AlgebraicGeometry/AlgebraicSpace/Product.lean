/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Limits.Yoneda
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Products of algebraic spaces

The binary product of algebraic spaces over a scheme `S` is the algebraic space whose functor of
points is the functor-category product of the functors of points. This is a product in the
category of algebraic spaces over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Functor-of-points binary products exist in the presheaf category on schemes over `S`. -/
instance instHasBinaryProductsFunctorOfPoints {S : Scheme.{u}} :
    HasBinaryProducts ((Over S)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-- The diagonal of a product of functors is represented by the product of the
represented pullbacks of its two projections. -/
theorem product_representableDiagonal {S : Scheme.{u}} (F G : AlgebraicSpace S)
    (hF : yoneda.relativelyRepresentable (Limits.diag F.functorOfPoints))
    (hG : yoneda.relativelyRepresentable (Limits.diag G.functorOfPoints)) :
    yoneda.relativelyRepresentable
      (Limits.diag (F.functorOfPoints ⨯ G.functorOfPoints)) := by
  apply Functor.relativelyRepresentable.diag_of_map_from_obj
  intro A x B y
  let xF := x ≫ prod.fst
  let yF := y ≫ prod.fst
  let xG := x ≫ prod.snd
  let yG := y ≫ prod.snd
  let rF := Functor.relativelyRepresentable.of_diag hF xF
  let rG := Functor.relativelyRepresentable.of_diag hG xG
  let aMap : rF.pullback yF ⟶ A ⨯ B :=
    prod.lift (rF.fst' yF) (rF.snd yF)
  let bMap : rG.pullback yG ⟶ A ⨯ B :=
    prod.lift (rG.fst' yG) (rG.snd yG)
  let W := Limits.pullback aMap bMap
  let fst : yoneda.obj W ⟶ yoneda.obj A :=
    yoneda.map (Limits.pullback.fst aMap bMap ≫ rF.fst' yF)
  let snd : W ⟶ B :=
    Limits.pullback.fst aMap bMap ≫ rF.snd yF
  refine ⟨W, snd, fst, ?_⟩
  let hFcond : ∀ c : PullbackCone x y,
      c.fst ≫ xF = c.snd ≫ yF := fun c ↦ by
    simpa only [xF, yF, Category.assoc] using
      congrArg (fun k ↦ k ≫ prod.fst) c.condition
  let hGcond : ∀ c : PullbackCone x y,
      c.fst ≫ xG = c.snd ≫ yG := fun c ↦ by
    simpa only [xG, yG, Category.assoc] using
      congrArg (fun k ↦ k ≫ prod.snd) c.condition
  let lift : ∀ c : PullbackCone x y, c.pt ⟶ yoneda.obj W := fun c ↦
    (yoneda.map_isPullback (IsPullback.of_hasPullback aMap bMap)).lift
      ((rF.isPullback yF).lift c.fst c.snd (hFcond c))
      ((rG.isPullback yG).lift c.fst c.snd (hGcond c))
      (by
        apply (cancel_mono (prodComparison yoneda A B)).1
        apply prod.hom_ext
        · simpa only [aMap, bMap, Category.assoc, ← yoneda.map_comp, prod.lift_fst,
            prodComparison_fst, rF.map_fst', rG.map_fst'] using
            ((rF.isPullback yF).lift_fst c.fst c.snd (hFcond c)).trans
              ((rG.isPullback yG).lift_fst c.fst c.snd (hGcond c)).symm
        · simpa only [aMap, bMap, Category.assoc, ← yoneda.map_comp, prod.lift_snd,
            prodComparison_snd] using
            ((rF.isPullback yF).lift_snd c.fst c.snd (hFcond c)).trans
              ((rG.isPullback yG).lift_snd c.fst c.snd (hGcond c)).symm)
  exact IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (fst := fst) (snd := yoneda.map snd) (by sorry) lift
    (by sorry) (by sorry) (by sorry))

/-- The product of the stored atlases of two algebraic spaces is an explicit
étale locally-surjective atlas for their functor product. -/
theorem productAtlas_exists {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ (F.functorOfPoints ⨯ G.functorOfPoints)),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := by
  let U := F.atlas.choose
  let V := G.atlas.choose
  let p := F.atlas.choose_spec.choose
  let q := G.atlas.choose_spec.choose
  refine ⟨U ⨯ V, prodComparison yoneda U V ≫ prod.map p q, ?_, ?_⟩
  · refine ⟨Functor.relativelyRepresentable.of_diag
      (product_representableDiagonal F G F.representableDiagonal G.representableDiagonal)
      (prodComparison yoneda U V ≫ prod.map p q), ?_⟩
    sorry
  · sorry

/-- The algebraic space `F × G` obtained as the sheaf product of algebraic spaces `F` and `G`
over `S`. -/
def product {S : Scheme.{u}} (F G : AlgebraicSpace S) : AlgebraicSpace S :=
  ofFunctor (F.functorOfPoints ⨯ G.functorOfPoints) sorry
    (product_representableDiagonal F G F.representableDiagonal G.representableDiagonal)
    (productAtlas_exists F G)

/-- The functor of points of `product F G` is the functor-category product of the functors of
points of `F` and `G`. -/
@[simp]
theorem product_functorOfPoints {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    (product F G).functorOfPoints = (F.functorOfPoints ⨯ G.functorOfPoints) := sorry

/-- The algebraic space `product F G` is an fppf sheaf with representable diagonal and a
representable étale locally-surjective atlas. -/
theorem product_spec {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    let X := product F G
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := by
  dsimp
  exact ⟨(product F G).isSheaf, (product F G).representableDiagonal, (product F G).atlas⟩

/-- The first projection `F × G ⟶ F`. -/
def productFst {S : Scheme.{u}} (F G : AlgebraicSpace S) : product F G ⟶ F :=
  (prod.fst : (F.functorOfPoints ⨯ G.functorOfPoints) ⟶ F.functorOfPoints)

/-- The second projection `F × G ⟶ G`. -/
def productSnd {S : Scheme.{u}} (F G : AlgebraicSpace S) : product F G ⟶ G :=
  (prod.snd : (F.functorOfPoints ⨯ G.functorOfPoints) ⟶ G.functorOfPoints)

/-- The morphism `E ⟶ F × G` induced by a pair of morphisms `E ⟶ F` and `E ⟶ G`. -/
def productLift {S : Scheme.{u}} {E F G : AlgebraicSpace S} (f : E ⟶ F) (g : E ⟶ G) :
    E ⟶ product F G :=
  (prod.lift f g : E.functorOfPoints ⟶ (F.functorOfPoints ⨯ G.functorOfPoints))

/-- Postcomposing `productLift f g` with the first projection recovers `f`. -/
theorem productFst_lift {S : Scheme.{u}} {E F G : AlgebraicSpace S} (f : E ⟶ F) (g : E ⟶ G) :
    productLift f g ≫ productFst F G = f := sorry

/-- Postcomposing `productLift f g` with the second projection recovers `g`. -/
theorem productSnd_lift {S : Scheme.{u}} {E F G : AlgebraicSpace S} (f : E ⟶ F) (g : E ⟶ G) :
    productLift f g ≫ productSnd F G = g := sorry

/-- A morphism into `product F G` is uniquely determined by its composites with the projections. -/
theorem productLift_uniq {S : Scheme.{u}} {E F G : AlgebraicSpace S} (f : E ⟶ F) (g : E ⟶ G)
    (k : E ⟶ product F G) (h₁ : k ≫ productFst F G = f) (h₂ : k ≫ productSnd F G = g) :
    k = productLift f g := sorry

/-- The atlas morphism `U × V ⟶ F × G` induced by Yoneda sections `p : U ⟶ F` and `q : V ⟶ G`. -/
def productAtlas {S : Scheme.{u}} {F G : AlgebraicSpace S} {U V : Over S}
    (p : yoneda.obj U ⟶ F.functorOfPoints) (q : yoneda.obj V ⟶ G.functorOfPoints) :
    yoneda.obj (U ⨯ V) ⟶ (product F G).functorOfPoints :=
  prodComparison yoneda U V ≫ prod.map p q

/-- If `p : U ⟶ F` and `q : V ⟶ G` are étale and étale-locally surjective, then so is the
atlas map `U × V ⟶ F × G`. -/
theorem productAtlas_spec {S : Scheme.{u}} {F G : AlgebraicSpace S} {U V : Over S}
    (p : yoneda.obj U ⟶ F.functorOfPoints) (q : yoneda.obj V ⟶ G.functorOfPoints)
    (hp_etale : MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p)
    (hp_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)
    (hq_etale : MorphismProperty.presheaf (MorphismProperty.over (@Etale)) q)
    (hq_surj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) q) :
    MorphismProperty.presheaf (MorphismProperty.over (@Etale)) (productAtlas p q) ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) (productAtlas p q) := by
  refine ⟨⟨Functor.relativelyRepresentable.of_diag
    (product F G).representableDiagonal (productAtlas p q), ?_⟩, ?_⟩
  · sorry
  · sorry

/-- The binary fan of the projections of `product F G` is a limit in the category of algebraic
spaces over `S`. -/
def product_isLimit {S : Scheme.{u}} (F G : AlgebraicSpace S) :
    IsLimit (BinaryFan.mk (productFst F G) (productSnd F G)) where
  lift s := productLift (BinaryFan.fst s) (BinaryFan.snd s)
  fac := sorry
  uniq := sorry

/-- Binary products of algebraic spaces over `S` exist, with product object `product F G`. -/
instance instHasBinaryProduct {S : Scheme.{u}} {F G : AlgebraicSpace S} :
    HasBinaryProduct F G :=
  HasLimit.mk
    { cone := BinaryFan.mk (productFst F G) (productSnd F G)
      isLimit := product_isLimit F G }

/-- The category of algebraic spaces over `S` has all binary products. -/
instance instHasBinaryProducts {S : Scheme.{u}} :
    HasBinaryProducts (AlgebraicSpace S) :=
  hasBinaryProducts_of_hasLimit_pair (AlgebraicSpace S)

end AlgebraicGeometry.AlgebraicSpace
