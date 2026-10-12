/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.StackInSets
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Basic

/-!
# The canonical quotient atlas and its groupoid-arrow comparison

The constructions retain their original public names and concrete data.
Existing proposition-valued laws remain explicit proof obligations.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open Functor.IsFibered.InGroupoids.Stackification
open CategoryTheory.Pseudofunctor.CoGrothendieck
open scoped CategoryTheory.Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The prestack `[U/_p R]` associated to a groupoid in algebraic spaces, as the co-Grothendieck
projection of the groupoid-valued functor of points. -/
def preQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor (groupoidPresheafProjection G.points)

/-- The total functor `𝒮_U ⟶ [U/_p R]` sending a functor-of-points value of `U` to the
corresponding object of the co-Grothendieck prestack. Fibre maps are identity arrows of
the discrete fibration `𝒮_U`. -/
def atlasToPreQuotientFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (stackInSets G.U.left).total ⥤ (preQuotient G).total where
  obj x :=
    { base := x.unop.fst.unop
      fiber := yonedaEquiv.symm x.unop.snd }
  map {x y} f :=
    { base := f.unop.val.unop
      fiber :=
        { arrow := yonedaEquiv.symm x.unop.snd ≫ G.e.left
          source := sorry
          target := sorry } }
  map_id := sorry
  map_comp := sorry

/-- The scheme-valued arrow carried by an object of `𝒮_R`. -/
def spacePointArrow {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (x : (stackInSets G.R.left).total) :
    ofOver x.unop.fst.unop ⟶ G.R.left :=
  yonedaEquiv.symm x.unop.snd

/-- The canonical cartesian `1`-morphism `𝒮_U ⟶ [U/_p R]`. -/
def atlasToPreQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.U.left).p (preQuotient G).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (atlasToPreQuotientFunctor G) sorry)

/-- The canonical cartesian `1`-morphism `𝒮_U ⟶ [U/R]` into the selected fppf quotient stack. -/
def fppfAtlas {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.U.left).p (fppfQuotientStack G).p :=
  (atlasToPreQuotient G).comp (fppfQuotientStackPresentation G).comparison

/-- The prestack composite `π_p ∘ s : 𝒮_R ⟶ [U/_p R]`. -/
abbrev preAtlasSource {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (preQuotient G).p :=
  (stackInSets.map G.s.left).comp (atlasToPreQuotient G)

/-- The prestack composite `π_p ∘ t : 𝒮_R ⟶ [U/_p R]`. -/
abbrev preAtlasTarget {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.R.left).p (preQuotient G).p :=
  (stackInSets.map G.t.left).comp (atlasToPreQuotient G)

/-- The fibre isomorphism of `[U/_p R]` associated to an `𝒮_R`-point: the underlying arrow is the
scheme-valued point of `R`, with source `s` and target `t`. -/
def sourceTargetPreHom {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (x : (stackInSets G.R.left).total) :
    (preAtlasSource G).toFunctor.obj x ⟶ (preAtlasTarget G).toFunctor.obj x where
  base := 𝟙 ((preAtlasSource G).toFunctor.obj x).base
  fiber := SpacePointHom.ofArrow (spacePointArrow G x) sorry sorry

/-- The atlas `𝒮_U ⟶ [U/R]` after aligning `𝒮_U` to the Hom-universe of `[U/R]`. -/
def fppfAtlasULift {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSetsULift G.U.left).p (fppfQuotientStack G).p :=
  (stackInSetsULift.down G.U.left).comp (fppfAtlas G)

end AlgebraicGeometry.GroupoidAlgebraicSpace
