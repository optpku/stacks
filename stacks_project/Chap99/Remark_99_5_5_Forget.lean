module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.BasedCategory.Basic
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom.OneCell
public import stacks_project.Chap99.Lemma_99_5_2
public import stacks_project.Chap110.Lemma_110_53_1

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

/-- The projection `(T, g, F) ↦ (T, g)` from the category of coherent sheaves on
`X / B` to schemes over `B`. -/
def toSchemesOver (f : X ⟶ B) [FinitePresentation f] : Obj f ⥤ SchemesOver B where
  obj x := x.σ
  map α := α.base
  map_id := sorry
  map_comp := sorry

/-- The object part of `toSchemesOver` is the test scheme of a coherent sheaf. -/
theorem toSchemesOver_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (toSchemesOver f).obj x = x.σ :=
  sorry

/-- The morphism part of `toSchemesOver` is the underlying map of schemes over `B`. -/
theorem toSchemesOver_map {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    (toSchemesOver f).map α = α.base :=
  sorry

/-- Forgetting the structure map of a scheme over `B` recovers the projection to `Over S`. -/
theorem toSchemesOver_comp_proj (f : X ⟶ B) [FinitePresentation f] :
    toSchemesOver f ⋙ CostructuredArrow.proj (ofOverFunctor S) B = p f :=
  sorry

/-- The functor-of-points section of a morphism of algebraic spaces from a scheme over `S`. -/
def functorOfPointsSection {T : Over S} (φ : ofOver T ⟶ B) :
    B.functorOfPoints.obj (op T) :=
  yonedaEquiv (φ : yoneda.obj T ⟶ B.functorOfPoints)

/-- `functorOfPointsSection φ` is the Yoneda evaluation of `φ`. -/
theorem functorOfPointsSection_eq {T : Over S} (φ : ofOver T ⟶ B) :
    functorOfPointsSection φ = yonedaEquiv (φ : yoneda.obj T ⟶ B.functorOfPoints) :=
  sorry

/-- The category-of-elements object classified by the structure map of a coherent sheaf. -/
def toBaseElement {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    B.functorOfPoints.Elements :=
  ⟨op x.σ.left, functorOfPointsSection x.σ.hom⟩

/-- The first component of `toBaseElement x` is the opposite of the test scheme of `x`. -/
theorem toBaseElement_fst {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    (toBaseElement x).fst = op x.σ.left :=
  sorry

/-- The second component of `toBaseElement x` is the functor-of-points section of the
structure map of `x`. -/
theorem toBaseElement_snd {f : X ⟶ B} [FinitePresentation f] (x : Obj f) :
    (toBaseElement x).snd = functorOfPointsSection x.σ.hom :=
  sorry

/-- Compatibility of functor-of-points sections with a morphism of coherent sheaves. -/
theorem toBaseHom_map_snd {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    B.functorOfPoints.map α.base.left.op (functorOfPointsSection y.σ.hom) =
      functorOfPointsSection x.σ.hom :=
  sorry

/-- The category-of-elements morphism induced by a morphism of coherent sheaves, pointing
from the target test scheme to the source so that its opposite lies over `α.base.left`. -/
def toBaseHom {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    toBaseElement y ⟶ toBaseElement x :=
  CategoryOfElements.homMk (toBaseElement y) (toBaseElement x) α.base.left.op
    (toBaseHom_map_snd α)

/-- The underlying morphism of `toBaseHom α` is the opposite of the test-scheme map of `α`. -/
theorem toBaseHom_val {f : X ⟶ B} [FinitePresentation f] {x y : Obj f} (α : x ⟶ y) :
    (toBaseHom α).val = α.base.left.op :=
  sorry

/-- The total functor of the 1-morphism `Coh_{X/B} ⟶ 𝒮_B`, sending a coherent sheaf to the
universe-lifted functor-of-points element of its structure map. -/
def toBaseFunctor (f : X ⟶ B) [FinitePresentation f] :
    Obj f ⥤ ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ where
  obj x := ULiftHom.objUp (op (toBaseElement x))
  map α := ULiftHom.up.map (Quiver.Hom.op (toBaseHom α))
  map_id := sorry
  map_comp := sorry

/-- On objects, `toBaseFunctor` is `ULiftHom.objUp` of the opposite category-of-elements
object. -/
theorem toBaseFunctor_obj (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (toBaseFunctor f).obj x = ULiftHom.objUp (op (toBaseElement x)) :=
  sorry

/-- `toBaseFunctor` lies strictly over `(Sch/S)`. -/
theorem toBaseFunctor_p (f : X ⟶ B) [FinitePresentation f] :
    toBaseFunctor f ⋙ Classifying.toGroupoidsProjection B = p f :=
  sorry

/-- The 1-morphism `Coh_{X/B} ⟶ 𝒮_B` of stacks in groupoids over `(Sch/S)_fppf`, sending
`(T, g, F)` to `(T, g)`. The target is the universe-aligned classifying fibration of `B`,
which presents `𝒮_B` in the Hom-universe of `toGroupoids`. -/
def toBase (f : X ⟶ B) [FinitePresentation f] :
    toGroupoids f ⟶ Classifying.toGroupoids B :=
  ofBasedFunctor (BasedFunctor.ofFunctor (toBaseFunctor f) (toBaseFunctor_p f))

/-- The total functor of `toBase f` is `toBaseFunctor f`. -/
theorem toBase_toFunctor (f : X ⟶ B) [FinitePresentation f] :
    toFunctor (toBase f) = toBaseFunctor f :=
  sorry

/-- `toBase f` lies strictly over `(Sch/S)`. -/
theorem toBase_p (f : X ⟶ B) [FinitePresentation f] :
    toFunctor (toBase f) ⋙ (Classifying.toGroupoids B).p = p f :=
  sorry

/-- `toBase` forgets the module and records the test scheme of `toSchemesOver`. -/
theorem toBase_spec (f : X ⟶ B) [FinitePresentation f] (x : Obj f) :
    (Classifying.toGroupoidsProjection B).obj ((toFunctor (toBase f)).obj x) =
      ((toSchemesOver f).obj x).left :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
