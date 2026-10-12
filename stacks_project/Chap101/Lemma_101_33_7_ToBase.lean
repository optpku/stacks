/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Elements
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import stacks_project.Chap94.Definition_94_12_1_AlgebraicStack
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Remark_94_16_3_Flat
public import stacks_project.Chap94.Remark_94_16_3_LocallyOfFinitePresentation

/-!
# Structure morphism of a quotient stack

The canonical `1`-morphism `[U / R] ⟶ 𝒮_B` associated to a groupoid in algebraic
spaces, as a morphism of categories fibred in groupoids over `Over S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open Functor.IsFibered.InGroupoids.Stackification Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- An algebraic space, viewed as a category fibred in groupoids, is a stack on
the big fppf site. -/
instance instIsStackOnSite_toGroupoids {S : Scheme.{u}} (B : AlgebraicSpace S) :
    IsStack.OnSite (Scheme.fppfTopology.over S) B.toGroupoids.p :=
  IsStack.InGroupoids.toOnSite inferInstance

end AlgebraicGeometry.AlgebraicStack

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The total functor `[U /ₚ R] ⟶ 𝒮_B` sending a point of `U` to its image in `B`
under the structure morphism, and sending arrows of `R` to identities in the
discrete fibre of `𝒮_B`. -/
def preQuotientToBaseFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.preQuotient.total ⥤ B.toGroupoids.total where
  obj x := op ⟨op x.base, G.U.hom.app (op x.base) x.fiber⟩
  map {x y} f :=
    (homMk ⟨op y.base, G.U.hom.app (op y.base) y.fiber⟩
        ⟨op x.base, G.U.hom.app (op x.base) x.fiber⟩ f.base.op sorry).op
  map_id := sorry
  map_comp := sorry

/-- On objects, `preQuotientToBaseFunctor` applies the structure morphism `U ⟶ B`. -/
theorem preQuotientToBaseFunctor_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : G.preQuotient.total) :
    (preQuotientToBaseFunctor G).obj x =
      op ⟨op x.base, G.U.hom.app (op x.base) x.fiber⟩ :=
  sorry

/-- The canonical `1`-morphism `[U /ₚ R] ⟶ 𝒮_B`. -/
def preQuotientToBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : G.preQuotient ⟶ B.toGroupoids :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedFunctor.ofFunctor (preQuotientToBaseFunctor G) sorry)

/-- The total functor of `preQuotientToBase` is `preQuotientToBaseFunctor`. -/
theorem preQuotientToBase_toFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.toFunctor (preQuotientToBase G) =
      preQuotientToBaseFunctor G :=
  sorry

/-- The selected stackification lift of `preQuotientToBase` through
`[U /ₚ R] ⟶ [U / R]`. -/
def toBaseLift {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := G.stackificationPresentation.comparison)
      (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor (preQuotientToBase G)) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    G.stackificationPresentation.isStackification
    (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor (preQuotientToBase G))

/-- The canonical structure morphism `[U / R] ⟶ 𝒮_B` obtained by lifting
`[U /ₚ R] ⟶ 𝒮_B` through stackification. -/
def toBase {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.quotientStack ⟶ B.toGroupoids :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor (toBaseLift G).lift.toBasedFunctor

/-- `toBase G` is a based functor over `Over S`. -/
theorem toBase_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.toFunctor G.toBase ⋙ B.toGroupoids.p =
      G.quotientStack.p :=
  sorry

/-- Reconstruct a `2`-isomorphism of groupoid-fibred morphisms from an isomorphism of
underlying based functors. -/
def ofBasedNatTransIso {S : Scheme.{u}} {X Y : GroupoidsOver S} {F G : X ⟶ Y}
    (e : FiberedCategoryOver.Groupoids.toBasedFunctor F ≅
      FiberedCategoryOver.Groupoids.toBasedFunctor G) : F ≅ G where
  hom := FiberedCategoryOver.Groupoids.ofBasedNatTrans e.hom
  inv := FiberedCategoryOver.Groupoids.ofBasedNatTrans e.inv
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The based functor of `stackificationHom ≫ toBase` is the precomposed lift. -/
theorem stackificationHom_comp_toBase_toBasedFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (G.stackificationHom ≫ G.toBase) =
      ((CartesianBasedFunctor.precomp B.toGroupoids.p
          G.stackificationPresentation.comparison).obj
        (toBaseLift G).lift).toBasedFunctor :=
  sorry

/-- The based functor of `preQuotientToBase` is that of its cartesian view. -/
theorem preQuotientToBase_toBasedFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.toBasedFunctor (preQuotientToBase G) =
      (FiberedCategoryOver.Groupoids.toCartesianBasedFunctor
        (preQuotientToBase G)).toBasedFunctor :=
  sorry

/-- Precomposing `toBase` with stackification recovers `preQuotientToBase`. -/
def stackificationHom_comp_toBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.stackificationHom ≫ G.toBase ≅ preQuotientToBase G :=
  ofBasedNatTransIso
    (eqToIso (stackificationHom_comp_toBase_toBasedFunctor G) ≪≫
      (CartesianBasedFunctor.forget G.preQuotient.p B.toGroupoids.p).mapIso
        (toBaseLift G).comparison ≪≫
      (eqToIso (preQuotientToBase_toBasedFunctor G)).symm)

/-- Associativity alignment for the atlas composite through stackification. -/
theorem atlas_comp_toBase_assoc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.atlas ≫ G.toBase =
      G.atlasToPreQuotient ≫ (G.stackificationHom ≫ G.toBase) :=
  sorry

/-- Before stackification, the atlas composite is the `1`-morphism associated to `U ⟶ B`. -/
theorem atlasToPreQuotient_comp_preQuotientToBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.atlasToPreQuotient ≫ preQuotientToBase G =
      AlgebraicSpace.toGroupoids.map G.U.hom :=
  sorry

/-- The composite `𝒮_U ⟶ [U / R] ⟶ 𝒮_B` is identified with the `1`-morphism associated
to the structure morphism `U ⟶ B`. -/
def atlas_comp_toBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.atlas ≫ G.toBase ≅ AlgebraicSpace.toGroupoids.map G.U.hom :=
  eqToIso (atlas_comp_toBase_assoc G) ≪≫
    whiskerLeftIso G.atlasToPreQuotient (stackificationHom_comp_toBase G) ≪≫
    eqToIso (atlasToPreQuotient_comp_preQuotientToBase G)

/-- Flatness of `G ⟶ B` implies flatness of the action groupoid. -/
instance instFlat_ofAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)
    [AlgebraicSpace.Flat G.X.hom] : Flat (ofAction G X) :=
  sorry

/-- Local finite presentation of `G ⟶ B` implies local finite presentation of the
action groupoid. -/
instance instLocallyOfFinitePresentation_ofAction {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : GroupAlgebraicSpace.Action G)
    [AlgebraicSpace.LocallyOfFinitePresentation G.X.hom] :
    LocallyOfFinitePresentation (ofAction G X) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
