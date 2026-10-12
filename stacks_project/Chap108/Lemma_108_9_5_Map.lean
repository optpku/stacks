/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Elements
public import stacks_project.Chap108.Lemma_108_8_3_Map
public import stacks_project.Chap108.Lemma_108_9_1_Map

/-!
# Structure morphism of the Picard functor

The forgetful 1-morphism `Pic_{X/B} ⟶ B` in the Hom-universe of
`Classifying.toGroupoids`, sending a sheafified fibrewise isomorphism class of
invertible modules on a fibre of `f` to the functor-of-points element of the
underlying test scheme over `B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open AlgebraicGeometry.GroupScheme
open FiberedCategoryOver.Groupoids
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativePicard

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The universe-raised functor of points of an algebraic space, as an fppf sheaf
on `(Sch/S)`. -/
def toBaseTarget (B : AlgebraicSpace S) :
    Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)) :=
  ⟨B.functorOfPoints ⋙ uliftFunctor.{u + 1, u}, sorry⟩

/-- The underlying presheaf of `toBaseTarget B` is the universe-raised functor of
points of `B`. -/
theorem toBaseTarget_obj (B : AlgebraicSpace S) :
    (toBaseTarget B).obj = B.functorOfPoints ⋙ uliftFunctor.{u + 1, u} :=
  sorry

/-- The functor-of-points section of the structure map of a Picard fibre object
over a test scheme `T`. -/
def toBaseIsoClass (f : X ⟶ B) {T : Over S} (x : (Picard.p f).Fiber T) :
    B.functorOfPoints.obj (op T) :=
  B.functorOfPoints.map (eqToHom (congrArg Opposite.op x.property))
    (Picard.functorOfPointsSection x.val.σ.hom)

/-- The presheaf map sending a fibrewise isomorphism class of invertible modules
on a fibre of `f` to the universe-lifted functor-of-points element of its
structure map. -/
def toBasePresheaf (f : X ⟶ B) :
    Functor.fiberIsoClassPresheaf (Picard.p f) ⟶ (toBaseTarget B).obj where
  app T := TypeCat.ofHom fun x ↦ ULift.up (toBaseIsoClass f (Quotient.out x))
  naturality := sorry

/-- On a represented fibrewise isomorphism class, `toBasePresheaf` is `ULift.up`
of `toBaseIsoClass`. -/
theorem toBaseIsoClass_mk (f : X ⟶ B) {T : Over S} (x : (Picard.p f).Fiber T) :
    (toBasePresheaf f).app (op T) (Quotient.mk'' x) =
      ULift.up (toBaseIsoClass f x) :=
  sorry

/-- The component of `toBasePresheaf` at a test scheme is `ULift.up` of
`toBaseIsoClass` of a chosen representative. -/
theorem toBasePresheaf_app (f : X ⟶ B) (T : (Over S)ᵒᵖ)
    (x : (Functor.fiberIsoClassPresheaf (Picard.p f)).obj T) :
    (toBasePresheaf f).app T x = ULift.up (toBaseIsoClass f (Quotient.out x)) :=
  sorry

/-- The sheaf morphism `functorOver f ⟶ toBaseTarget B` obtained by sheafifying
`toBasePresheaf`. -/
def toBaseSheaf (f : X ⟶ B) : functorOver f ⟶ toBaseTarget B :=
  ((sheafificationAdjunction (Scheme.fppfTopology.over S) (Type (u + 1))).homEquiv
      (Functor.fiberIsoClassPresheaf (Picard.p f)) (toBaseTarget B)).symm
    (toBasePresheaf f)

/-- The category-of-elements object classified by the structure map of a
sheafified Picard isomorphism class. -/
def toBaseElement (f : X ⟶ B) (x : (functorOver f).obj.Elements) :
    B.functorOfPoints.Elements :=
  ⟨x.1, ULift.down ((toBaseSheaf f).hom.app x.1 x.2)⟩

/-- The first component of `toBaseElement x` is the test scheme of `x`. -/
theorem toBaseElement_fst (f : X ⟶ B) (x : (functorOver f).obj.Elements) :
    (toBaseElement f x).fst = x.1 :=
  sorry

/-- The second component of `toBaseElement x` is the underlying functor-of-points
section of the sheaf map `toBaseSheaf`. -/
theorem toBaseElement_snd (f : X ⟶ B) (x : (functorOver f).obj.Elements) :
    (toBaseElement f x).snd = ULift.down ((toBaseSheaf f).hom.app x.1 x.2) :=
  sorry

/-- The functor on categories of elements induced by `toBaseSheaf`, landing in
the functor of points of `B`. -/
def toBaseElementsMap (f : X ⟶ B) :
    (functorOver f).obj.Elements ⥤ B.functorOfPoints.Elements where
  obj x := toBaseElement f x
  map φ := ⟨φ.val, sorry⟩
  map_id := sorry
  map_comp := sorry

/-- The universe-lifted category-of-elements projection of the Picard functor. -/
def toGroupoidsProjection (f : X ⟶ B) :
    ULiftHom.{u + 1} (functorOver f).obj.Elementsᵒᵖ ⥤ Over S :=
  (ULiftHom.down : ULiftHom.{u + 1} (functorOver f).obj.Elementsᵒᵖ ⥤
      (functorOver f).obj.Elementsᵒᵖ) ⋙
    (CategoryOfElements.π (functorOver f).obj).leftOp

/-- The universe-lifted category-of-elements projection of the Picard functor is
fibred in groupoids. -/
instance toGroupoidsProjection.instIsFiberedInGroupoids (f : X ⟶ B) :
    Functor.IsFibered.InGroupoids (toGroupoidsProjection f) :=
  sorry

/-- The discrete stack of the Picard functor, in the Hom-universe of
`Classifying.toGroupoids`. -/
def toGroupoids (f : X ⟶ B) :
    FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u + 1} (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor (toGroupoidsProjection f)

/-- The projection of `toGroupoids f` is the universe-lifted category-of-elements
projection of `functorOver f`. -/
theorem toGroupoids_p (f : X ⟶ B) :
    (toGroupoids f).p = toGroupoidsProjection f :=
  sorry

/-- The total functor of the structure morphism `Pic_{X/B} ⟶ B`, sending a
sheafified Picard class to the universe-lifted functor-of-points element of its
structure map. -/
def toBaseFunctor (f : X ⟶ B) :
    ULiftHom.{u + 1} (functorOver f).obj.Elementsᵒᵖ ⥤
      ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ :=
  (ULiftHom.down : ULiftHom.{u + 1} (functorOver f).obj.Elementsᵒᵖ ⥤
      (functorOver f).obj.Elementsᵒᵖ) ⋙
    (toBaseElementsMap f).op ⋙
    (ULiftHom.up : B.functorOfPoints.Elementsᵒᵖ ⥤
      ULiftHom.{u + 1} B.functorOfPoints.Elementsᵒᵖ)

/-- `toBaseFunctor` lies strictly over `(Sch/S)`. -/
theorem toBaseFunctor_p (f : X ⟶ B) :
    toBaseFunctor f ⋙ Classifying.toGroupoidsProjection B = toGroupoidsProjection f :=
  sorry

/-- The structure 1-morphism `Pic_{X/B} ⟶ B` in the Hom-universe of
`Classifying.toGroupoids`, forgetting the invertible module and recording the
test scheme over `B`. -/
def toBase (f : X ⟶ B) : toGroupoids f ⟶ Classifying.toGroupoids B :=
  ofBasedFunctor { toFunctor := toBaseFunctor f, w := sorry }

/-- The total functor of `toBase f` is `toBaseFunctor f`. -/
theorem toBase_toFunctor (f : X ⟶ B) :
    toFunctor (toBase f) = toBaseFunctor f :=
  sorry

/-- `toBase f` lies strictly over `(Sch/S)`. -/
theorem toBase_p (f : X ⟶ B) :
    toFunctor (toBase f) ⋙ (Classifying.toGroupoids B).p = (toGroupoids f).p :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativePicard
