module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.CategoryOfElements.Forward
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import stacks_project.Chap65.Lemma_65_9_1
public import stacks_project.Chap78.Definition_78_20_1_Quotient

/-!
# Atlas and structure morphisms of a quotient stack

This module constructs the canonical cartesian `1`-morphisms `𝒮_U ⟶ [U/R]` and
`[U/R] ⟶ 𝒮_B` associated to a groupoid in algebraic spaces, together with the
identifying `2`-isomorphism against the morphism induced by `U ⟶ B`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open Functor.IsFibered.InGroupoids.Stackification
open scoped CategoryTheory.Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The stack in sets `𝒮_X` associated to an algebraic space, obtained from its functor of
points as an fppf sheaf on `Sch/S`. -/
def stackInSets {S : Scheme.{u}} (X : AlgebraicSpace S) :
    StackOver.Sets (Scheme.fppfTopology.over S) :=
  (StackOver.Sets.ofSheaf (Scheme.fppfTopology.over S)).obj X.toSheaf

/-- `stackInSets X` is the category-of-elements stack of the fppf sheaf of points of `X`. -/
theorem stackInSets_eq {S : Scheme.{u}} (X : AlgebraicSpace S) :
    stackInSets X =
      (StackOver.Sets.ofSheaf (Scheme.fppfTopology.over S)).obj X.toSheaf :=
  sorry

/-- The projection of `𝒮_X` is the opposite category-of-elements projection of the functor
of points. -/
theorem stackInSets_p {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (stackInSets X).p = (CategoryOfElements.π X.functorOfPoints).leftOp :=
  sorry

/-- The site-level stack condition of `𝒮_X` on `(Sch/S)_fppf`. -/
instance instIsStackOnSite_stackInSets {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsStack.OnSite (Scheme.fppfTopology.over S) (stackInSets X).p :=
  IsStack.InSets.toOnSite inferInstance

/-- The cartesian `1`-morphism `𝒮_X ⟶ 𝒮_Y` induced by a morphism of algebraic spaces. -/
def stackInSets.map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    CartesianBasedFunctor (stackInSets X).p (stackInSets Y).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor
      (StackOver.Sets.Hom.toFunctor
        ((StackOver.Sets.ofSheaf (Scheme.fppfTopology.over S)).map (Sheaf.homEquiv.symm f)))
      sorry)

/-- The identity morphism of algebraic spaces induces the identity on `𝒮_X`. -/
theorem stackInSets.map_id {S : Scheme.{u}} (X : AlgebraicSpace S) :
    stackInSets.map (𝟙 X) = CartesianBasedFunctor.id (stackInSets X).p :=
  sorry

/-- The cartesian `1`-morphism associated to a composite of morphisms of algebraic spaces is
the composite of the associated cartesian `1`-morphisms. -/
theorem stackInSets.map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    stackInSets.map (f ≫ g) = (stackInSets.map f).comp (stackInSets.map g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

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

/-- The base of `atlasToPreQuotientFunctor G x` is the scheme underlying the point `x`. -/
theorem atlasToPreQuotientFunctor_base {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.U.left).total) :
    ((atlasToPreQuotientFunctor G).obj x).base = x.unop.fst.unop :=
  sorry

/-- The fibre of `atlasToPreQuotientFunctor G x` is the scheme-valued point associated to the
functor-of-points value of `x`. -/
theorem atlasToPreQuotientFunctor_fiber {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (stackInSets G.U.left).total) :
    ((atlasToPreQuotientFunctor G).obj x).fiber = yonedaEquiv.symm x.unop.snd :=
  sorry

/-- The canonical cartesian `1`-morphism `𝒮_U ⟶ [U/_p R]`. -/
def atlasToPreQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.U.left).p (preQuotient G).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (atlasToPreQuotientFunctor G) sorry)

/-- The total functor of `atlasToPreQuotient` is `atlasToPreQuotientFunctor`. -/
theorem atlasToPreQuotient_toFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (atlasToPreQuotient G).toFunctor = atlasToPreQuotientFunctor G :=
  sorry

/-- The atlas `1`-morphism `π : 𝒮_U ⟶ [U/R]`, obtained by composing the object inclusion
into `[U/_p R]` with stackification. -/
def atlas {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (stackInSets G.U.left).p (quotientStack G).p :=
  (atlasToPreQuotient G).comp (stackificationPresentation G).comparison

/-- The atlas factors as the object inclusion into `[U/_p R]` followed by stackification. -/
theorem atlas_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    atlas G = (atlasToPreQuotient G).comp (stackificationPresentation G).comparison :=
  sorry

/-- The total functor `[U/_p R] ⟶ 𝒮_B` sending a point of `U` to its image in `B` under the
structure morphism, and sending arrows of `R` to identities in the discrete fibre of `𝒮_B`. -/
def preQuotientToBaseFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (preQuotient G).total ⥤ (stackInSets B).total where
  obj x :=
    op ⟨op x.base, yonedaEquiv (x.fiber ≫ G.U.hom)⟩
  map {x y} f :=
    (homMk ⟨op y.base, yonedaEquiv (y.fiber ≫ G.U.hom)⟩
        ⟨op x.base, yonedaEquiv (x.fiber ≫ G.U.hom)⟩ f.base.op sorry).op
  map_id := sorry
  map_comp := sorry

/-- On objects, `preQuotientToBaseFunctor` applies the structure morphism `U ⟶ B`. -/
theorem preQuotientToBase_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (preQuotient G).total) :
    (preQuotientToBaseFunctor G).obj x =
      op ⟨op x.base, yonedaEquiv (x.fiber ≫ G.U.hom)⟩ :=
  sorry

/-- On arrows, `preQuotientToBaseFunctor` uses only the underlying base morphism of the
co-Grothendieck arrow. -/
theorem preQuotientToBase_map_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : (preQuotient G).total}
    (f : x ⟶ y) :
    ((preQuotientToBaseFunctor G).map f).unop.val = f.base.op :=
  sorry

/-- The canonical cartesian `1`-morphism `[U/_p R] ⟶ 𝒮_B`. -/
def preQuotientToBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (preQuotient G).p (stackInSets B).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (preQuotientToBaseFunctor G) sorry)

/-- The total functor of `preQuotientToBase` is `preQuotientToBaseFunctor`. -/
theorem preQuotientToBase_toFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (preQuotientToBase G).toFunctor = preQuotientToBaseFunctor G :=
  sorry

/-- The selected stackification lift of `preQuotientToBase` through `[U/_p R] ⟶ [U/R]`. -/
def toBaseLift {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (stackificationPresentation G).comparison) (preQuotientToBase G) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (stackificationPresentation G).isStackification (preQuotientToBase G)

/-- The canonical cartesian `1`-morphism `[U/R] ⟶ 𝒮_B` obtained by lifting
`[U/_p R] ⟶ 𝒮_B` through stackification. -/
def toBase {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (quotientStack G).p (stackInSets B).p :=
  (toBaseLift G).lift

/-- Precomposing `toBase` with stackification recovers `preQuotientToBase`. -/
def toBase_comp {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (CartesianBasedFunctor.precomp (stackInSets B).p
          (stackificationPresentation G).comparison).obj (toBase G) ≅
      preQuotientToBase G :=
  (toBaseLift G).comparison

/-- Associativity alignment for the atlas composite through stackification. -/
theorem atlas_comp_toBase_assoc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (atlas G).comp (toBase G) =
      (atlasToPreQuotient G).comp
        ((stackificationPresentation G).comparison.comp (toBase G)) :=
  sorry

/-- Before stackification, the atlas composite is the `1`-morphism associated to `U ⟶ B`. -/
theorem atlasToPreQuotient_comp_preQuotientToBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (atlasToPreQuotient G).comp (preQuotientToBase G) = stackInSets.map G.U.hom :=
  sorry

/-- The composite `𝒮_U ⟶ [U/R] ⟶ 𝒮_B` is identified with the cartesian `1`-morphism
associated to the structure morphism `U ⟶ B`. -/
def atlas_comp_toBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (atlas G).comp (toBase G) ≅ stackInSets.map G.U.hom :=
  eqToIso (atlas_comp_toBase_assoc G) ≪≫
    (CartesianBasedFunctor.precomp (stackInSets B).p (atlasToPreQuotient G)).mapIso
      (toBaseLift G).comparison ≪≫
    eqToIso (atlasToPreQuotient_comp_preQuotientToBase G)

/-- `atlas_comp_toBase` is the whiskered stackification comparison, after aligning
composites with the structure morphism of `U ⟶ B`. -/
theorem atlas_comp_toBase_eq {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    atlas_comp_toBase G =
      eqToIso (atlas_comp_toBase_assoc G) ≪≫
        (CartesianBasedFunctor.precomp (stackInSets B).p (atlasToPreQuotient G)).mapIso
          (toBaseLift G).comparison ≪≫
        eqToIso (atlasToPreQuotient_comp_preQuotientToBase G) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
