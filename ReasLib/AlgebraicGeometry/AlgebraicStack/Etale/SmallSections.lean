/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Logic.Small.Basic
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.DirectImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.AtlasCharts
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction
public import ReasLib.CategoryTheory.Fibered.Groupoids.UnderlyingFunctorIso
public import ReasLib.CategoryTheory.Fibered.PseudoPullback.Basic.Computations
public import ReasLib.CategoryTheory.Fibered.Representable.Slice.Map
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic

/-!
# Small étale direct-image sections for algebraic stacks

A smooth scheme atlas of the source and the representable
diagonal of the target provide an actual scheme object of each comma category.
Compatible sections are determined by evaluation on this object: smooth
surjective atlases have étale local sections and the scheme atlas of the
representing algebraic space is étale surjective. The coefficient carrier is
therefore small without a size assertion for arbitrary presheaves.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open FiberedCategoryOver.Groupoids
open scoped Bicategory BasedFunctor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack.EtaleSmallSections

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}

/-- The relative product over the base is the target of the diagonal. -/
private abbrev relativeProduct (Y : GroupoidsOver S) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)
    (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)

/-- The scheme atlas directly supplied by the source algebraic-stack witness. -/
private def sourceAtlas (X : GroupoidsOver S) [hX : AlgebraicStack X] : Over S :=
  Classical.choose hX.existsSmoothSurjectiveAtlas

/-- The atlas morphism retained by that same supplied witness. -/
private def sourceAtlasMap (X : GroupoidsOver S) [hX : AlgebraicStack X] :
    GroupoidsOver.slice (sourceAtlas X) ⟶ X :=
  Classical.choose (Classical.choose_spec hX.existsSmoothSurjectiveAtlas)

/-- The base product used to test the target's supplied diagonal. -/
private def pairScheme (X : GroupoidsOver S) [AlgebraicStack X] (y : Y.total) : Over S :=
  prod (sourceAtlas X) (Y.p.obj y)

/-- The first target object over the product comes from the actual source atlas. -/
private def sourceMap [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) :
    GroupoidsOver.slice (pairScheme X y) ⟶ Y :=
  (overMap (prod.fst : pairScheme X y ⟶ sourceAtlas X) ≫ sourceAtlasMap X) ≫ f

/-- The second target object comes from the Yoneda representative of the original
 target object, retaining its actual identity-fibre comparison. -/
private def targetMap [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) :
    GroupoidsOver.slice (pairScheme X y) ⟶ Y :=
  overMap (prod.snd : pairScheme X y ⟶ Y.p.obj y) ≫
    YonedaSlice.representative (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y))

/-- The atlas-source map retains the scheme over `S` of each product-slice object. -/
private theorem sourceMap_base_obj [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    Y.p.obj ((toFunctor (sourceMap f y)).obj q) = q.left :=
  congrArg (fun G => G.obj q) (comm (sourceMap f y))

/-- The Yoneda-target map retains the same scheme over `S`. -/
private theorem targetMap_base_obj [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    Y.p.obj ((toFunctor (targetMap f y)).obj q) = q.left :=
  congrArg (fun G => G.obj q) (comm (targetMap f y))

/-- The base comparison is the image of the two actual base identifications
through the explicit section of the closed identity fibration. -/
private def pairBaseIso [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    (toFunctor (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)).obj
        ((toFunctor (sourceMap f y)).obj q) ≅
      (toFunctor (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)).obj
        ((toFunctor (targetMap f y)).obj q) :=
  (FiberedCategoryOver.Groupoids.baseSection.{u + 1, u, u + 1} (Over S)).mapIso
    (eqToIso (sourceMap_base_obj f y q) ≪≫ (eqToIso (targetMap_base_obj f y q)).symm)

/-- The explicit base comparison is vertical over the identity of the common
product-slice scheme. -/
private theorem pairBaseIso_hom_isHomLift [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    (FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S)).p.IsHomLift
      (𝟙 q.left) (pairBaseIso f y q).hom := by
  apply IsHomLift.of_fac'
    (FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S)).p
    (𝟙 q.left) (pairBaseIso f y q).hom
    (sourceMap_base_obj f y q) (targetMap_base_obj f y q)
  change eqToHom (sourceMap_base_obj f y q) ≫
      eqToHom (targetMap_base_obj f y q).symm = _
  simp
  rfl

/-- Pair the two actual target objects over their common base. -/
private def pairObject [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    (relativeProduct Y).total :=
  BasedCategory.PseudoPullback.mk (toBasedFunctor (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y))
    (toBasedFunctor (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)) q.left
    { fst := ⟨(toFunctor (sourceMap f y)).obj q, sourceMap_base_obj f y q⟩
      snd := ⟨(toFunctor (targetMap f y)).obj q, targetMap_base_obj f y q⟩
      iso := Functor.Fiber.isoMk (pairBaseIso f y q) (pairBaseIso_hom_isHomLift f y q) }

/-- The two target maps define a functor into the relative product. -/
private def pairFunctor [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) :
    (GroupoidsOver.slice (pairScheme X y)).total ⥤
      (relativeProduct Y).total where
  obj := pairObject f y
  map {q r} α := BasedCategory.PseudoPullback.Hom.mk α.left
    ((toFunctor (sourceMap f y)).map α)
    (by
      letI : (GroupoidsOver.slice (pairScheme X y)).p.IsHomLift α.left α :=
        Functor.IsHomLift.map α
      exact BasedFunctor.preserves_isHomLift (toBasedFunctor (sourceMap f y)) α.left α)
    ((toFunctor (targetMap f y)).map α)
    (by
      letI : (GroupoidsOver.slice (pairScheme X y)).p.IsHomLift α.left α :=
        Functor.IsHomLift.map α
      exact BasedFunctor.preserves_isHomLift (toBasedFunctor (targetMap f y)) α.left α)
    (by
      constructor
      change Y.p.map ((toFunctor (sourceMap f y)).map α) ≫
          (eqToHom (sourceMap_base_obj f y r) ≫ eqToHom (targetMap_base_obj f y r).symm) =
        (eqToHom (sourceMap_base_obj f y q) ≫ eqToHom (targetMap_base_obj f y q).symm) ≫
          Y.p.map ((toFunctor (targetMap f y)).map α)
      letI : (GroupoidsOver.slice (pairScheme X y)).p.IsHomLift α.left α :=
        Functor.IsHomLift.map α
      letI := BasedFunctor.preserves_isHomLift (toBasedFunctor (sourceMap f y)) α.left α
      letI := BasedFunctor.preserves_isHomLift (toBasedFunctor (targetMap f y)) α.left α
      rw [IsHomLift.fac' Y.p α.left ((toFunctor (sourceMap f y)).map α),
        IsHomLift.fac' Y.p α.left ((toFunctor (targetMap f y)).map α)]
      simp)
  map_id := by
    intro q
    apply BasedCategory.PseudoPullback.hom_ext
    · change (toFunctor (sourceMap f y)).map (𝟙 q) = _
      exact (toFunctor (sourceMap f y)).map_id q
    · change (toFunctor (targetMap f y)).map (𝟙 q) = _
      exact (toFunctor (targetMap f y)).map_id q
  map_comp := by
    intro q r t α β
    apply BasedCategory.PseudoPullback.hom_ext
    · change (toFunctor (sourceMap f y)).map (α ≫ β) = _
      exact (toFunctor (sourceMap f y)).map_comp α β
    · change (toFunctor (targetMap f y)).map (α ≫ β) = _
      exact (toFunctor (targetMap f y)).map_comp α β

/-- The actual product-scheme pair is the test map for the original target
 diagonal witness. -/
private def pairMap [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) :
    GroupoidsOver.slice (pairScheme X y) ⟶
      relativeProduct Y :=
  let F : BasedFunctor (toBasedCategory (GroupoidsOver.slice (pairScheme X y)))
      (toBasedCategory (relativeProduct Y)) :=
    { toFunctor := pairFunctor f y
      w := rfl }
  ofBasedFunctor F

/-- The actual diagonal-pullback groupoid-fibred category. -/
private abbrev diagonalFibre [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (pairMap f y)
    (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)

/-- The space selected directly from the target's supplied diagonal field. -/
private def fibreSpace [AlgebraicStack X] [hY : AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    AlgebraicSpace S :=
  Classical.choose (hY.representableDiagonal (pairMap f y))

/-- The representing algebraic space maps to the product scheme. -/
private def fibreSpaceMap [AlgebraicStack X] [hY : AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    fibreSpace f y ⟶ AlgebraicSpace.ofOver (pairScheme X y) :=
  Classical.choose (Classical.choose_spec (hY.representableDiagonal (pairMap f y)))

/-- The diagonal fibre is equivalent to the groupoid of its representing
algebraic space. -/
private def fibreEquivalence [AlgebraicStack X] [hY : AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    diagonalFibre f y ≌
      (fibreSpace f y).toGroupoids :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec
      (hY.representableDiagonal (pairMap f y))))

/-- The specified scheme atlas point of the selected representing algebraic space. -/
private def fibreAtlasPoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (fibreSpace f y).toGroupoids.total :=
  op ⟨op (AlgebraicSpace.SmallEtale.AtlasCharts.atlasOver (fibreSpace f y)),
    yonedaEquiv (AlgebraicSpace.SmallEtale.AtlasCharts.atlasMap (fibreSpace f y))⟩

/-- Move the actual atlas point through the supplied inverse equivalence. -/
private def diagonalAtlasPoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (diagonalFibre f y).total :=
  (toFunctor (fibreEquivalence f y).inv).obj (fibreAtlasPoint f y)

/-- The product-scheme point stored by that diagonal-pullback object. -/
private def atlasProductPoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (GroupoidsOver.slice (pairScheme X y)).total :=
  (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (pairMap f y)
    (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y))).obj (diagonalAtlasPoint f y)

/-- The original source object at which compatible sections will be evaluated. -/
private def atlasSourcePoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    X.total :=
  (toFunctor (sourceAtlasMap X)).obj
    ((Over.map (prod.fst : pairScheme X y ⟶ sourceAtlas X)).obj (atlasProductPoint f y))

/-- The middle target object stored by the diagonal pullback point. -/
private def atlasMiddlePoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    Y.total :=
  (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (pairMap f y)
    (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y))).obj (diagonalAtlasPoint f y)

/-- The actual diagonal-pullback comparison at the selected atlas point. -/
private def atlasPairIso [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (toFunctor (pairMap f y)).obj (atlasProductPoint f y) ≅
      (toFunctor (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)).obj (atlasMiddlePoint f y) :=
  (toFunctorIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} (pairMap f y)
    (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y))).app (diagonalAtlasPoint f y)

/-- Project the diagonal comparison to an isomorphism between the two original
 target objects over the product-scheme atlas point. -/
private def atlasTargetIso [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (toFunctor (sourceMap f y)).obj (atlasProductPoint f y) ≅
      (toFunctor (targetMap f y)).obj (atlasProductPoint f y) :=
  (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y) (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y))).mapIso
      (atlasPairIso f y) ≪≫
    (ObjectProperty.FullSubbicategory.toFunctor.compIso
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)
        (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y) (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y))).symm.app (atlasMiddlePoint f y) ≪≫
    (toFunctorIso (Hom.diagonal.fstIso.{u + 1, u, u + 1} (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y))).app (atlasMiddlePoint f y) ≪≫
    (toFunctorIso (Hom.diagonal.sndIso.{u + 1, u, u + 1} (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y))).symm.app (atlasMiddlePoint f y) ≪≫
    (ObjectProperty.FullSubbicategory.toFunctor.compIso
        (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)
        (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y) (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y))).app (atlasMiddlePoint f y) ≪≫
    ((toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y) (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y))).mapIso
      (atlasPairIso f y)).symm

/-- The original arrow from the actual source atlas object into the target
 object, through the stored product projection and Yoneda counit. -/
private def atlasArrow [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (toFunctor f).obj (atlasSourcePoint f y) ⟶ y :=
  (atlasTargetIso f y).hom ≫
    (toFunctor (YonedaSlice.representative (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y)))).map
      (Over.mkIdTerminal.from
        ((Over.map (prod.snd : pairScheme X y ⟶ Y.p.obj y)).obj (atlasProductPoint f y))) ≫
    (YonedaSlice.representative.fiberObjIso (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y))).hom.1

/-- The real scheme atlas as an object of the original direct-image comma
 category. The original target object and its arrow are retained. -/
private def atlasIndex [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    StructuredArrow (op y) (toFunctor f).op :=
  StructuredArrow.mk (atlasArrow f y).op

/-- Evaluation of a compatible family at that actual atlas object. -/
private def evaluation [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (F : Sheaf X.etaleTopology (Type u)) (y : Y.total) :
    (StructuredArrow.proj (op y) (toFunctor f).op ⋙ F.obj).sections →
      F.obj.obj (op (atlasSourcePoint f y)) :=
  fun s ↦ s.1 (atlasIndex f y)

/-- The smooth source atlas has étale local sections; the scheme atlas of its
 fibre over the target chart is étale surjective. Thus every original comma
 object is locally connected to the selected atlas object, and the sheaf
 separation law makes evaluation injective. -/
private theorem evaluation_injective [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (F : Sheaf X.etaleTopology (Type u)) (y : Y.total) :
    Function.Injective (evaluation f F y) :=
  sorry

/-- Compatible sections of a small-valued étale sheaf along a morphism of
algebraic stacks form a small type. -/
theorem sectionsSmall [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (F : Sheaf X.etaleTopology (Type u)) (y : Y.total) :
    Small.{u} (StructuredArrow.proj (op y) (toFunctor f).op ⋙ F.obj).sections :=
  small_of_injective (evaluation_injective f F y)

end AlgebraicGeometry.AlgebraicStack.EtaleSmallSections

namespace AlgebraicGeometry.GroupoidsOver

/-- Algebraic-stack atlases and diagonal witnesses give the actual sheaf-section
 size certificate needed by the canonical étale direct image. -/
instance hasSmallCFGTypeSections_of_algebraicStack {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) :
    HasSmallCFGTypeSections (S := S) f where
  small F y := by
    rw [cartesian_toFunctor_eq]
    exact AlgebraicStack.EtaleSmallSections.sectionsSmall f F y.unop

end AlgebraicGeometry.GroupoidsOver
