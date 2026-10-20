module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Atlas
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Precomposition
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification

/-!
# The structure morphism of a quotient stack

The structure morphism of a groupoid over an algebraic space induces a cartesian morphism
from its fppf quotient stack to the stack of points of that space. Its composite with the
quotient atlas is identified with the morphism induced on stacks of points.
-/

@[expose] public section

-- Local declaration justification (metaprogramming implementation): exposed data definitions
-- must reference private map laws and the selected lift under Lean's module visibility rules.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite
open scoped CategoryTheory.Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A prestack object determines a point of the base algebraic space via the structure map. -/
private def preQuotientToBaseObj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (preQuotient G).total) :
    (stackInSets B).total :=
  op ⟨op x.base, yonedaEquiv (x.fiber ≫ G.U.hom)⟩

/-- The images in the base algebraic space of a prestack arrow's endpoints agree after
restriction along its underlying scheme morphism. -/
private theorem preQuotientToBaseMap_compatible {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : (preQuotient G).total} (f : x ⟶ y) :
    B.functorOfPoints.map f.base.op (yonedaEquiv (y.fiber ≫ G.U.hom)) =
      yonedaEquiv (x.fiber ≫ G.U.hom) := sorry

/-- A prestack arrow determines the unique arrow of base points over its scheme morphism. -/
private def preQuotientToBaseMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : (preQuotient G).total} (f : x ⟶ y) :
    preQuotientToBaseObj G x ⟶ preQuotientToBaseObj G y :=
  (homMk ⟨op y.base, yonedaEquiv (y.fiber ≫ G.U.hom)⟩
    ⟨op x.base, yonedaEquiv (x.fiber ≫ G.U.hom)⟩ f.base.op
    (preQuotientToBaseMap_compatible G f)).op

/-- The map from prestack arrows to arrows of base points preserves identities. -/
private theorem preQuotientToBaseMap_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (preQuotient G).total) :
    preQuotientToBaseMap G (𝟙 x) = 𝟙 (preQuotientToBaseObj G x) := sorry

/-- The map from prestack arrows to arrows of base points preserves composition. -/
private theorem preQuotientToBaseMap_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y z : (preQuotient G).total}
    (f : x ⟶ y) (g : y ⟶ z) :
    preQuotientToBaseMap G (f ≫ g) =
      preQuotientToBaseMap G f ≫ preQuotientToBaseMap G g := sorry

/-- The total functor from the groupoid prestack to the stack of base points applies the
structure morphism on objects and sends vertical groupoid arrows to identities. -/
def preQuotientToBaseFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (preQuotient G).total ⥤ (stackInSets B).total where
  obj := preQuotientToBaseObj G
  map := preQuotientToBaseMap G
  map_id := preQuotientToBaseMap_id G
  map_comp := preQuotientToBaseMap_comp G

/-- On objects, the prestack-to-base functor applies the structure morphism `U ⟶ B`. -/
theorem preQuotientToBase_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : (preQuotient G).total) :
    (preQuotientToBaseFunctor G).obj x =
      op ⟨op x.base, yonedaEquiv (x.fiber ≫ G.U.hom)⟩ := sorry

/-- The prestack-to-base functor sends an arrow to the arrow of points determined by its
underlying scheme morphism. -/
theorem preQuotientToBase_map_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : (preQuotient G).total} (f : x ⟶ y) :
    ((preQuotientToBaseFunctor G).map f).unop.val = f.base.op := sorry

/-- The prestack-to-base functor commutes with projection to the base scheme category. -/
private theorem preQuotientToBaseFunctor_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    preQuotientToBaseFunctor G ⋙ (stackInSets B).p = (preQuotient G).p := sorry

/-- The canonical cartesian morphism from the groupoid prestack to the stack of base points. -/
def preQuotientToBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (preQuotient G).p (stackInSets B).p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (preQuotientToBaseFunctor G) (preQuotientToBaseFunctor_over G))

/-- The selected lift of the prestack structure morphism through fppf stackification. -/
private def toBaseLift {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation G).comparison) (preQuotientToBase G) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (fppfQuotientStackPresentation G).isStackification (preQuotientToBase G)

/-- The structure morphism from the fppf quotient stack to the stack of base points. -/
def toBase {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor (fppfQuotientStack G).p (stackInSets B).p :=
  (toBaseLift G).lift

/-- Precomposing the quotient stack structure morphism with the stackification comparison
recovers the prestack structure morphism. -/
def toBase_comp {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (CartesianBasedFunctor.precomp (stackInSets B).p
      (fppfQuotientStackPresentation G).comparison).obj (toBase G) ≅ preQuotientToBase G :=
  (toBaseLift G).comparison

/-- Any lift of the prestack structure morphism with a specified comparison admits a unique
isomorphism from the selected structure morphism compatible with that comparison. -/
theorem toBase_unique {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B)
    (F : CartesianBasedFunctor (fppfQuotientStack G).p (stackInSets B).p)
    (α : (CartesianBasedFunctor.precomp (stackInSets B).p
      (fppfQuotientStackPresentation G).comparison).obj F ≅ preQuotientToBase G) :
    ∃! β : toBase G ≅ F,
      (CartesianBasedFunctor.precomp (stackInSets B).p
        (fppfQuotientStackPresentation G).comparison).mapIso β ≪≫ α = toBase_comp G := sorry

/-- The atlas composite can be reassociated through the stackification comparison. -/
private theorem atlas_comp_toBase_assoc {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (fppfAtlas G).comp (toBase G) =
      (atlasToPreQuotient G).comp
        ((fppfQuotientStackPresentation G).comparison.comp (toBase G)) := sorry

/-- The prestack atlas followed by the prestack structure morphism is the morphism of
stacks of points induced by the structure map `U ⟶ B`. -/
theorem atlasToPreQuotient_comp_preQuotientToBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (atlasToPreQuotient G).comp (preQuotientToBase G) = stackInSets.map G.U.hom := sorry

/-- The quotient atlas followed by the quotient structure morphism is naturally isomorphic
over the scheme base to the morphism of stacks of points induced by `U ⟶ B`. -/
def atlas_comp_toBase {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (fppfAtlas G).comp (toBase G) ≅ stackInSets.map G.U.hom :=
  eqToIso (atlas_comp_toBase_assoc G) ≪≫
    (CartesianBasedFunctor.precomp (stackInSets B).p (atlasToPreQuotient G)).mapIso
      (toBase_comp G) ≪≫
    eqToIso (atlasToPreQuotient_comp_preQuotientToBase G)

end AlgebraicGeometry.GroupoidAlgebraicSpace
