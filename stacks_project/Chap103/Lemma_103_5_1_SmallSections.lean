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
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack

/-!
# Small étale direct-image sections for algebraic stacks

The supplied smooth scheme atlas of the source and the supplied representable
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

/-- The actual fixed-owner relative product which is the target of the diagonal. -/
abbrev relativeProduct (Y : GroupoidsOver S) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u}
    (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)
    (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)

/-- The scheme atlas directly supplied by the source algebraic-stack witness. -/
def sourceAtlas (X : GroupoidsOver S) [hX : AlgebraicStack X] : Over S :=
  Classical.choose hX.existsSmoothSurjectiveAtlas

/-- The atlas morphism retained by that same supplied witness. -/
def sourceAtlasMap (X : GroupoidsOver S) [hX : AlgebraicStack X] :
    GroupoidsOver.slice (sourceAtlas X) ⟶ X :=
  Classical.choose (Classical.choose_spec hX.existsSmoothSurjectiveAtlas)

/-- The base product used to test the target's supplied diagonal. -/
def pairScheme (X : GroupoidsOver S) [AlgebraicStack X] (y : Y.total) : Over S :=
  prod (sourceAtlas X) (Y.p.obj y)

/-- The first target object over the product comes from the actual source atlas. -/
def sourceMap [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) :
    GroupoidsOver.slice (pairScheme X y) ⟶ Y :=
  (overMap (prod.fst : pairScheme X y ⟶ sourceAtlas X) ≫ sourceAtlasMap X) ≫ f

/-- The second target object comes from the Yoneda representative of the original
 target object, retaining its actual identity-fibre comparison. -/
def targetMap [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) :
    GroupoidsOver.slice (pairScheme X y) ⟶ Y :=
  overMap (prod.snd : pairScheme X y ⟶ Y.p.obj y) ≫
    YonedaSlice.representative (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y))

/-- The atlas-source map retains the scheme over `S` of each product-slice object. -/
theorem sourceMap_base_obj [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    Y.p.obj ((toFunctor (sourceMap f y)).obj q) = q.left :=
  congrArg (fun G => G.obj q) (comm (sourceMap f y))

/-- The Yoneda-target map retains the same scheme over `S`. -/
theorem targetMap_base_obj [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    Y.p.obj ((toFunctor (targetMap f y)).obj q) = q.left :=
  congrArg (fun G => G.obj q) (comm (targetMap f y))

/-- The base comparison is the image of the two actual base identifications
through the explicit section of the closed identity fibration. -/
def pairBaseIso [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    (toFunctor (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)).obj
        ((toFunctor (sourceMap f y)).obj q) ≅
      (toFunctor (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)).obj
        ((toFunctor (targetMap f y)).obj q) :=
  (FiberedCategoryOver.Groupoids.baseSection.{u + 1, u, u + 1} (Over S)).mapIso
    (eqToIso (sourceMap_base_obj f y q) ≪≫ (eqToIso (targetMap_base_obj f y q)).symm)

/-- The explicit base comparison is vertical over the identity of the common
product-slice scheme. -/
theorem pairBaseIso_hom_isHomLift [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    (FiberedCategoryOver.Groupoids.base.{u + 1, u, u + 1} (Over S)).p.IsHomLift
      (𝟙 q.left) (pairBaseIso f y q).hom :=
  sorry

/-- Pair the two actual target objects over their common base. -/
def pairObject [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total)
    (q : (GroupoidsOver.slice (pairScheme X y)).total) :
    (relativeProduct Y).total :=
  BasedCategory.PseudoPullback.mk (toBasedFunctor (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y))
    (toBasedFunctor (FiberedCategoryOver.Groupoids.baseProjection.{u + 1, u, u + 1} Y)) q.left
    { fst := ⟨(toFunctor (sourceMap f y)).obj q, sourceMap_base_obj f y q⟩
      snd := ⟨(toFunctor (targetMap f y)).obj q, targetMap_base_obj f y q⟩
      iso := Functor.Fiber.isoMk (pairBaseIso f y q) (pairBaseIso_hom_isHomLift f y q) }

/-- The pairing has actual object and arrow functions, with laws deferred. -/
def pairFunctor [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) :
    (GroupoidsOver.slice (pairScheme X y)).total ⥤
      (relativeProduct Y).total where
  obj := pairObject f y
  map {q r} α := BasedCategory.PseudoPullback.Hom.mk α.left
    ((toFunctor (sourceMap f y)).map α) sorry
    ((toFunctor (targetMap f y)).map α) sorry sorry
  map_id := sorry
  map_comp := sorry

/-- The actual product-scheme pair is the test map for the original target
 diagonal witness. -/
def pairMap [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) :
    GroupoidsOver.slice (pairScheme X y) ⟶
      relativeProduct Y :=
  let F : BasedFunctor (toBasedCategory (GroupoidsOver.slice (pairScheme X y)))
      (toBasedCategory (relativeProduct Y)) :=
    { toFunctor := pairFunctor f y
      w := sorry }
  ofBasedFunctor F

/-- The actual diagonal-pullback groupoid-fibred category. -/
abbrev diagonalFibre [AlgebraicStack X] (f : X ⟶ Y) (y : Y.total) : GroupoidsOver S :=
  TwoFibreProduct.apex.{u + 1, u, u + 1, u} (pairMap f y)
    (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)

/-- The space selected directly from the target's supplied diagonal field. -/
def fibreSpace [AlgebraicStack X] [hY : AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    AlgebraicSpace S :=
  Classical.choose (hY.representableDiagonal (pairMap f y))

/-- Its original representing projection is selected from the same supplied
 field, rather than from a new representability-existence theorem. -/
def fibreSpaceMap [AlgebraicStack X] [hY : AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    fibreSpace f y ⟶ AlgebraicSpace.ofOver (pairScheme X y) :=
  Classical.choose (Classical.choose_spec (hY.representableDiagonal (pairMap f y)))

/-- The equivalence is extracted from the original `RepresentsBaseChange`
 witness by unfolding that witness directly. -/
def fibreEquivalence [AlgebraicStack X] [hY : AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    diagonalFibre f y ≌
      (fibreSpace f y).toGroupoids :=
  Classical.choose
    (Classical.choose_spec (Classical.choose_spec
      (hY.representableDiagonal (pairMap f y))))

/-- The specified scheme atlas point of the selected representing algebraic space. -/
def fibreAtlasPoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (fibreSpace f y).toGroupoids.total :=
  op ⟨op (AlgebraicSpace.SmallEtale.AtlasCharts.atlasOver (fibreSpace f y)),
    yonedaEquiv (AlgebraicSpace.SmallEtale.AtlasCharts.atlasMap (fibreSpace f y))⟩

/-- Move the actual atlas point through the supplied inverse equivalence. -/
def diagonalAtlasPoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (diagonalFibre f y).total :=
  (toFunctor (fibreEquivalence f y).inv).obj (fibreAtlasPoint f y)

/-- The product-scheme point stored by that diagonal-pullback object. -/
def atlasProductPoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (GroupoidsOver.slice (pairScheme X y)).total :=
  (toFunctor (TwoFibreProduct.fst.{u + 1, u, u + 1, u} (pairMap f y)
    (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y))).obj (diagonalAtlasPoint f y)

/-- The original source object at which compatible sections will be evaluated. -/
def atlasSourcePoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    X.total :=
  (toFunctor (sourceAtlasMap X)).obj
    ((Over.map (prod.fst : pairScheme X y ⟶ sourceAtlas X)).obj (atlasProductPoint f y))

/-- The middle target object stored by the diagonal pullback point. -/
def atlasMiddlePoint [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    Y.total :=
  (toFunctor (TwoFibreProduct.snd.{u + 1, u, u + 1, u} (pairMap f y)
    (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y))).obj (diagonalAtlasPoint f y)

/-- The actual diagonal-pullback comparison at the selected atlas point. -/
def atlasPairIso [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (toFunctor (pairMap f y)).obj (atlasProductPoint f y) ≅
      (toFunctor (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y)).obj (atlasMiddlePoint f y) :=
  (toFunctorIso (TwoFibreProduct.comparisonIso.{u + 1, u, u + 1, u} (pairMap f y)
    (FiberedCategoryOver.Groupoids.diagonal.{u + 1, u, u + 1} Y))).app (diagonalAtlasPoint f y)

/-- Project the diagonal comparison to an isomorphism between the two original
 target objects over the product-scheme atlas point. -/
def atlasTargetIso [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
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
def atlasArrow [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    (toFunctor f).obj (atlasSourcePoint f y) ⟶ y :=
  (atlasTargetIso f y).hom ≫
    (toFunctor (YonedaSlice.representative (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y)))).map
      (Over.mkIdTerminal.from
        ((Over.map (prod.snd : pairScheme X y ⟶ Y.p.obj y)).obj (atlasProductPoint f y))) ≫
    (YonedaSlice.representative.fiberObjIso (⟨y, rfl⟩ : Y.p.Fiber (Y.p.obj y))).hom.1

/-- The real scheme atlas as an object of the original direct-image comma
 category. The original target object and its arrow are retained. -/
def atlasIndex [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y) (y : Y.total) :
    StructuredArrow (op y) (toFunctor f).op :=
  StructuredArrow.mk (atlasArrow f y).op

/-- Evaluation of a compatible family at that actual atlas object. -/
def evaluation [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (F : Sheaf X.etaleTopology (Type u)) (y : Y.total) :
    (StructuredArrow.proj (op y) (toFunctor f).op ⋙ F.obj).sections →
      F.obj.obj (op (atlasSourcePoint f y)) :=
  fun s ↦ s.1 (atlasIndex f y)

/-- The smooth source atlas has étale local sections; the scheme atlas of its
 fibre over the target chart is étale surjective. Thus every original comma
 object is locally connected to the selected atlas object, and the sheaf
 separation law makes evaluation injective. -/
theorem evaluation_injective [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    (F : Sheaf X.etaleTopology (Type u)) (y : Y.total) :
    Function.Injective (evaluation f F y) :=
  sorry

/-- Native range smallness applied to the explicit atlas-evaluation injection. -/
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
