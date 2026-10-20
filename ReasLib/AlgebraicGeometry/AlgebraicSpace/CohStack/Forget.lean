module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Representable

/-!
# Forgetful 1-morphism of the stack of coherent sheaves

The rule `(T, g, F) ↦ (T, g)` is the projection `Obj f ⥤ SchemesOver B`, and the
induced 1-morphism of categories fibred in groupoids over `Over S` lands in the
universe-aligned classifying fibration of `B`, which presents the stack in sets
`𝒮_B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupScheme Opposite
open CategoryTheory.BasedFunctor
open CategoryTheory.FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The base map of an identity coherent-sheaf morphism is the identity over the base. -/
theorem toSchemesOverMapId {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    (𝟙 x : x ⟶ x).base = 𝟙 x.σ := sorry

/-- The base map of a composite coherent-sheaf morphism is the composite of its base maps. -/
theorem toSchemesOverMapComp {f : X ⟶ B} [FinitePresentation f] {x y z : Obj f}
    (α : x ⟶ y) (β : y ⟶ z) :
    (α ≫ β).base = α.base ≫ β.base := sorry

/-- The projection `(T, g, F) ↦ (T, g)` from the category of coherent sheaves on
`X / B` to schemes over `B`. -/
def toSchemesOver (f : X ⟶ B) [FinitePresentation f] : Obj f ⥤ SchemesOver B where
  obj x := x.σ
  map α := α.base
  map_id := toSchemesOverMapId
  map_comp := toSchemesOverMapComp

/-- The object part of `toSchemesOver` is the test scheme of a coherent sheaf. -/
theorem toSchemesOver_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (toSchemesOver f).obj x = x.σ := sorry

/-- The morphism part of `toSchemesOver` is the underlying map of schemes over `B`. -/
theorem toSchemesOver_map {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    (toSchemesOver f).map α = α.base := sorry

/-- Forgetting the structure map of a scheme over `B` recovers the projection to `Over S`. -/
theorem toSchemesOver_comp_proj (f : X ⟶ B) [FinitePresentation f] :
    toSchemesOver f ⋙ CostructuredArrow.proj (ofOverFunctor S) B = p f := sorry

/-- The category-of-elements object classified by the structure map of a coherent sheaf. -/
def toBaseElement {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    B.functorOfPoints.Elements :=
  ⟨op x.σ.left, yonedaEquiv (x.σ.hom : yoneda.obj x.σ.left ⟶ B.functorOfPoints)⟩

/-- The first component of `toBaseElement x` is the opposite of the test scheme of `x`. -/
theorem toBaseElement_fst {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    (toBaseElement x).fst = op x.σ.left := sorry

/-- The second component of `toBaseElement x` is the functor-of-points section of the
structure map of `x`. -/
theorem toBaseElement_snd {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    (toBaseElement x).snd = yonedaEquiv (x.σ.hom : yoneda.obj x.σ.left ⟶ B.functorOfPoints) := sorry

/-- Compatibility of functor-of-points sections with a morphism of coherent sheaves. -/
theorem toBaseHom_map_snd {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    B.functorOfPoints.map α.base.left.op (yonedaEquiv (y.σ.hom : yoneda.obj y.σ.left ⟶ B.functorOfPoints)) =
      yonedaEquiv (x.σ.hom : yoneda.obj x.σ.left ⟶ B.functorOfPoints) := sorry

/-- The category-of-elements morphism induced by a morphism of coherent sheaves, pointing
from the target test scheme to the source so that its opposite lies over `α.base.left`. -/
def toBaseHom {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    toBaseElement y ⟶ toBaseElement x :=
  CategoryOfElements.homMk (toBaseElement y) (toBaseElement x) α.base.left.op
    (toBaseHom_map_snd α)

/-- The underlying morphism of `toBaseHom α` is the opposite of the test-scheme map of `α`. -/
theorem toBaseHom_val {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    (toBaseHom α).val = α.base.left.op := sorry

/-- A coherent-sheaf morphism induces the lifted opposite morphism of its structure-map elements. -/
def toBaseMap {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    (ULiftHom.objUp (op (toBaseElement x)) :
      ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ) ⟶
        ULiftHom.objUp (op (toBaseElement y)) :=
  ULiftHom.up.map (Quiver.Hom.op (toBaseHom α))

/-- The lifted structure-map morphism of an identity is the identity. -/
theorem toBaseMap_id {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    toBaseMap (𝟙 x) = 𝟙 (ULiftHom.objUp (op (toBaseElement x))) := sorry

/-- Lifted structure-map morphisms preserve composition. -/
theorem toBaseMap_comp {f : X ⟶ B} [FinitePresentation f] {x y z : Obj f}
    (α : x ⟶ y) (β : y ⟶ z) :
    toBaseMap (α ≫ β) = toBaseMap α ≫ toBaseMap β := sorry

/-- The total functor of the 1-morphism `Coh_{X/B} ⟶ 𝒮_B`, sending a coherent sheaf to the
universe-lifted functor-of-points element of its structure map. -/
def toBaseFunctor (f : X ⟶ B) [FinitePresentation f] :
    Obj f ⥤ ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ where
  obj x := ULiftHom.objUp (op (toBaseElement x))
  map α := toBaseMap α
  map_id := toBaseMap_id
  map_comp := toBaseMap_comp

/-- On objects, `toBaseFunctor` is `ULiftHom.objUp` of the opposite category-of-elements
object. -/
theorem toBaseFunctor_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (toBaseFunctor f).obj x = ULiftHom.objUp (op (toBaseElement x)) := sorry

/-- `toBaseFunctor` lies strictly over `(Sch/S)`. -/
theorem toBaseFunctor_p (f : X ⟶ B) [FinitePresentation f] :
    toBaseFunctor f ⋙ Classifying.toGroupoidsProjection B = p f := sorry

/-- The 1-morphism `Coh_{X/B} ⟶ 𝒮_B` of stacks in groupoids over `(Sch/S)_fppf`, sending
`(T, g, F)` to `(T, g)`. The target is the universe-aligned classifying fibration of `B`,
which presents `𝒮_B` in the Hom-universe of `toGroupoids`. -/
def toBase (f : X ⟶ B) [FinitePresentation f] :
    toGroupoids f ⟶ Classifying.toGroupoids B :=
  ofBasedFunctor (BasedFunctor.ofFunctor (toBaseFunctor f) (toBaseFunctor_p f))

/-- The total functor of `toBase f` is `toBaseFunctor f`. -/
theorem toBase_toFunctor (f : X ⟶ B) [FinitePresentation f] :
    toFunctor (toBase f) = toBaseFunctor f := sorry

/-- `toBase f` lies strictly over `(Sch/S)`. -/
theorem toBase_p (f : X ⟶ B) [FinitePresentation f] :
    toFunctor (toBase f) ⋙ (Classifying.toGroupoids B).p = p f := sorry

/-- `toBase` forgets the module and records the test scheme of `toSchemesOver`. -/
theorem toBase_spec (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (Classifying.toGroupoidsProjection B).obj ((toFunctor (toBase f)).obj x) =
      ((toSchemesOver f).obj x).left := sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
