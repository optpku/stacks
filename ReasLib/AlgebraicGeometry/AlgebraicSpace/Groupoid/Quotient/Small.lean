/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.FunctorPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Stackification

/-!
# Quotient stacks with small Hom types

The small groupoid-valued functor of points gives a prestack and an fppf quotient stack
in the original universe of categories fibred in groupoids over the base scheme.
-/

@[expose] public section

-- Exposed constructions use private endpoint and functor laws in their proof fields.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Limits Opposite AlgebraicSpace
open scoped Bicategory Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient

/-- The prestack `[U /ₚ R]` associated to a groupoid in algebraic spaces, obtained as the
co-Grothendieck construction of `groupoidPresheaf`. -/
def preQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    GroupoidsOver S :=
  FiberedCategoryOver.Groupoids.ofFunctor
    (Pseudofunctor.CoGrothendieck.groupoidPresheafProjection G.groupoidPresheaf)

/-- The projection of `[U /ₚ R]` is the co-Grothendieck projection of `groupoidPresheaf`. -/
theorem preQuotient_p {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (preQuotient G).p =
      Pseudofunctor.CoGrothendieck.groupoidPresheafProjection G.groupoidPresheaf :=
  sorry

/-- The selected stackification presentation of `[U /ₚ R]`. -/
def stackificationPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicGeometry.GroupoidsOver.Stackification.Presentation (preQuotient G).p :=
  AlgebraicGeometry.GroupoidsOver.Stackification.presentation (preQuotient G).p

/-- The comparison of `stackificationPresentation G` is a stackification of `[U /ₚ R]`. -/
theorem stackificationPresentation_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S)
      (stackificationPresentation G).comparison := sorry

/-- The quotient stack `[U / R]` associated to a groupoid in algebraic spaces, obtained by
stackifying `[U /ₚ R]`. -/
@[reducible]
def quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    GroupoidsOver S :=
  (stackificationPresentation G).target.toGroupoids

/-- The quotient stack is the target of the selected stackification of `[U /ₚ R]`. -/
theorem quotientStack_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    (quotientStack G) = (stackificationPresentation G).target.toGroupoids := sorry

/-- The quotient stack `[U / R]` is a stack in groupoids on the big fppf site of `S`. -/
@[reducible]
def quotientStack_isStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) (quotientStack G).p :=
  StackOver.Groupoids.isStack (stackificationPresentation G).target

/-- The stackification comparison `1`-morphism `[U /ₚ R] ⟶ [U / R]`. -/
def stackificationHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : (preQuotient G) ⟶ (quotientStack G) :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (stackificationPresentation G).comparison.toBasedFunctor

/-- `stackificationHom` is a stackification of `[U /ₚ R]`. -/
theorem stackificationHom_isStackification {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.Hom.IsStackification
      (Scheme.fppfTopology.over S) (stackificationHom G) := sorry

/-- A point of the object space defines an object of the groupoid prestack. -/
private def atlasToPreQuotientObj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : G.U.left.toGroupoids.total) :
    (preQuotient G).total where
  base := x.unop.fst.unop
  fiber := x.unop.snd

/-- Identity arrows have the endpoints prescribed by morphisms of points. -/
private theorem atlasToPreQuotientMap_endpoints {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : G.U.left.toGroupoids.total} (f : x ⟶ y) :
    G.s.left.app (op x.unop.fst.unop)
        (G.e.left.app (op x.unop.fst.unop) x.unop.snd) = x.unop.snd ∧
      G.t.left.app (op x.unop.fst.unop)
        (G.e.left.app (op x.unop.fst.unop) x.unop.snd) =
          (G.groupoidPresheaf.map f.unop.val).obj y.unop.snd := sorry

/-- A morphism of points defines a prestack arrow with its base map and an identity arrow. -/
private def atlasToPreQuotientMap {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y : G.U.left.toGroupoids.total} (f : x ⟶ y) :
    atlasToPreQuotientObj G x ⟶ atlasToPreQuotientObj G y where
  base := f.unop.val.unop
  fiber := FunctorPointHom.ofArrow
    (G.e.left.app (op x.unop.fst.unop) x.unop.snd)
    (atlasToPreQuotientMap_endpoints G f).1 (atlasToPreQuotientMap_endpoints G f).2

/-- The prestack arrow assigned to an identity of points is an identity. -/
private theorem atlasToPreQuotientMap_id {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : G.U.left.toGroupoids.total) :
    atlasToPreQuotientMap G (𝟙 x) = 𝟙 (atlasToPreQuotientObj G x) := sorry

/-- The prestack arrow assignment preserves composition of morphisms of points. -/
private theorem atlasToPreQuotientMap_comp {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {x y z : G.U.left.toGroupoids.total}
    (f : x ⟶ y) (g : y ⟶ z) :
    atlasToPreQuotientMap G (f ≫ g) =
      atlasToPreQuotientMap G f ≫ atlasToPreQuotientMap G g := sorry

/-- The point inclusion sends points of the object space to objects of the groupoid prestack. -/
def atlasToPreQuotientFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.U.left.toGroupoids.total ⥤ (preQuotient G).total where
  obj := atlasToPreQuotientObj G
  map := atlasToPreQuotientMap G
  map_id := atlasToPreQuotientMap_id G
  map_comp := atlasToPreQuotientMap_comp G

/-- The point inclusion preserves the underlying scheme of each point. -/
theorem atlasToPreQuotientFunctor_base {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : G.U.left.toGroupoids.total) :
    ((atlasToPreQuotientFunctor G).obj x).base = x.unop.fst.unop := sorry

/-- The point inclusion commutes with projection to schemes over the base. -/
private theorem atlasToPreQuotientFunctor_over {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    atlasToPreQuotientFunctor G ⋙ (preQuotient G).p = G.U.left.toGroupoids.p := sorry

/-- The canonical morphism from the object-space fibration to the groupoid prestack. -/
def atlasToPreQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : G.U.left.toGroupoids ⟶ preQuotient G :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedFunctor.ofFunctor (atlasToPreQuotientFunctor G) (atlasToPreQuotientFunctor_over G))

/-- The canonical atlas of the quotient stack is point inclusion followed by stackification. -/
def atlas {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.U.left.toGroupoids ⟶ quotientStack G :=
  atlasToPreQuotient G ≫ stackificationHom G

/-- The quotient atlas factors through the groupoid prestack and stackification. -/
theorem atlas_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    atlas G = atlasToPreQuotient G ≫ stackificationHom G := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace.SmallQuotient
