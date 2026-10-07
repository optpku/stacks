module

public import Mathlib.CategoryTheory.Groupoid.Grpd.Basic
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.Groupoids.Hom
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification
public import stacks_project.Chap78.Definition_78_11_1_Groupoid
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Quotient stacks of groupoids in algebraic spaces

This module constructs the groupoid-valued functor of points of a groupoid in algebraic
spaces, the associated prestack `[U /ₚ R]`, and its stackification `[U / R]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite AlgebraicSpace
open scoped Bicategory Pseudofunctor.CoGrothendieck

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- A morphism between two `T`-valued functor-of-points of a groupoid in algebraic spaces. -/
structure FunctorPointHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S}
    (x y : G.U.left.functorOfPoints.obj (op T)) where
  /-- The underlying `T`-valued arrow of `R`. -/
  arrow : G.R.left.functorOfPoints.obj (op T)
  /-- The arrow has source `x`. -/
  source : G.s.left.app (op T) arrow = x
  /-- The arrow has target `y`. -/
  target : G.t.left.app (op T) arrow = y

namespace FunctorPointHom

/-- Construct a morphism of functor-of-points from an arrow with specified endpoints. -/
def ofArrow {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (arrow : G.R.left.functorOfPoints.obj (op T))
    (source : G.s.left.app (op T) arrow = x)
    (target : G.t.left.app (op T) arrow = y) :
    G.FunctorPointHom x y :=
  ⟨arrow, source, target⟩

/-- The underlying arrow of `ofArrow` is the supplied arrow. -/
theorem ofArrow_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S}
    {x y : G.U.left.functorOfPoints.obj (op T)}
    (arrow : G.R.left.functorOfPoints.obj (op T))
    (source : G.s.left.app (op T) arrow = x)
    (target : G.t.left.app (op T) arrow = y) :
    (ofArrow arrow source target).arrow = arrow := sorry

/-- Morphisms of functor-of-points with the same underlying arrow are equal. -/
theorem ext {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    {f g : G.FunctorPointHom x y} (h : f.arrow = g.arrow) : f = g := sorry

/-- The Yoneda morphism `ofOver T ⟶ G.R.left` associated to a functor-of-points arrow. -/
def toHom {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) : ofOver T ⟶ G.R.left :=
  yonedaEquiv.symm f.arrow

/-- `toHom` is the Yoneda equivalent of the underlying arrow. -/
theorem toHom_eq {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) :
    f.toHom = yonedaEquiv.symm f.arrow := sorry

/-- The composite `T`-valued arrow of two composable morphisms of functor-of-points, obtained
by converting to morphisms over `B`, applying groupoid composition, and returning to
functor-of-points. -/
def compArrow {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) (g : G.FunctorPointHom y z) :
    G.R.left.functorOfPoints.obj (op T) :=
  let σ : ofOver T ⟶ B := yonedaEquiv.symm (G.R.hom.app (op T) f.arrow)
  let later : Over.mk σ ⟶ G.R := Over.homMk g.toHom sorry
  let earlier : Over.mk σ ⟶ G.R := Over.homMk f.toHom sorry
  yonedaEquiv ((G.compose later earlier sorry).left :
    yoneda.obj T ⟶ G.R.left.functorOfPoints)

/-- The composite morphism of functor-of-points. -/
def comp {S : Scheme.{u}} {B : AlgebraicSpace S} {G : GroupoidAlgebraicSpace B}
    {T : Over S} {x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) (g : G.FunctorPointHom y z) :
    G.FunctorPointHom x z :=
  ofArrow (compArrow f g) sorry sorry

/-- The underlying arrow of a composite is `compArrow`. -/
theorem comp_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G : GroupoidAlgebraicSpace B} {T : Over S}
    {x y z : G.U.left.functorOfPoints.obj (op T)}
    (f : G.FunctorPointHom x y) (g : G.FunctorPointHom y z) :
    (f.comp g).arrow = compArrow f g := sorry

end FunctorPointHom

/-- The explicit groupoid structure on the `T`-valued functor-of-points of a groupoid in
algebraic spaces. -/
@[reducible]
def functorPointGroupoid {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) :
    CategoryTheory.Groupoid.{u, u} (G.U.left.functorOfPoints.obj (op T)) where
  Hom := fun x y ↦ G.FunctorPointHom x y
  id := fun x ↦
    { arrow := G.e.left.app (op T) x
      source := sorry
      target := sorry }
  comp := fun f g ↦ f.comp g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry
  inv := fun f ↦
    { arrow := G.i.left.app (op T) f.arrow
      source := sorry
      target := sorry }
  inv_comp := sorry
  comp_inv := sorry

/-- The bundled groupoid of `T`-valued functor-of-points of a groupoid in algebraic spaces. -/
def functorPoints {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    (T : Over S) : Grpd.{u, u} :=
  ⟨G.U.left.functorOfPoints.obj (op T), G.functorPointGroupoid T⟩

/-- Morphisms in `functorPointGroupoid G T` are `FunctorPointHom`. -/
theorem functorPointGroupoid_hom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S)
    (x y : G.U.left.functorOfPoints.obj (op T)) :
    (G.functorPointGroupoid T).Hom x y = G.FunctorPointHom x y := sorry

/-- The objects of `functorPoints G T` are the `T`-valued points of `U`. -/
theorem functorPoints_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) :
    (G.functorPoints T : Type u) = G.U.left.functorOfPoints.obj (op T) := sorry

/-- The functor of points of a groupoid in algebraic spaces, valued in bundled groupoids.
On objects it sends `T` to the groupoid `(U(T), R(T), s, t, c)`. -/
def groupoidPresheaf {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (Over S)ᵒᵖ ⥤ Grpd.{u, u} where
  obj T := G.functorPoints T.unop
  map f :=
    { obj := fun x ↦ G.U.left.functorOfPoints.map f x
      map := fun p ↦
        { arrow := G.R.left.functorOfPoints.map f p.arrow
          source := sorry
          target := sorry }
      map_id := sorry
      map_comp := sorry }
  map_id := sorry
  map_comp := sorry

/-- The objects of the point groupoid over `T` are the `T`-valued points of `U`. -/
theorem groupoidPresheaf_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (T : Over S) :
    (G.groupoidPresheaf.obj (op T) : Type u) = G.U.left.functorOfPoints.obj (op T) :=
  sorry

/-- Restriction of objects in `groupoidPresheaf` is restriction of functor-of-points of `U`. -/
theorem groupoidPresheaf_map_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : (Over S)ᵒᵖ} (f : T ⟶ T')
    (x : G.U.left.functorOfPoints.obj T) :
    (G.groupoidPresheaf.map f).obj x = G.U.left.functorOfPoints.map f x := sorry

/-- Restriction of arrows in `groupoidPresheaf` is restriction of functor-of-points of `R`. -/
theorem groupoidPresheaf_map_arrow {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T T' : Over S} (f : op T ⟶ op T')
    {x y : G.U.left.functorOfPoints.obj (op T)} (p : G.FunctorPointHom x y) :
    ((G.groupoidPresheaf.map f).map p).arrow = G.R.left.functorOfPoints.map f p.arrow :=
  sorry

/-- The prestack `[U /ₚ R]` associated to a groupoid in algebraic spaces, obtained as the
co-Grothendieck construction of `groupoidPresheaf`. -/
def preQuotient {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    GroupoidsOver S :=
  FiberedCategoryOver.Groupoids.ofFunctor
    (Pseudofunctor.CoGrothendieck.groupoidPresheafProjection G.groupoidPresheaf)

/-- The projection of `[U /ₚ R]` is the co-Grothendieck projection of `groupoidPresheaf`. -/
theorem preQuotient_p {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.preQuotient.p =
      Pseudofunctor.CoGrothendieck.groupoidPresheafProjection G.groupoidPresheaf :=
  sorry

/-- The selected stackification presentation of `[U /ₚ R]`. -/
def stackificationPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    Functor.IsFibered.InGroupoids.Stackification.Presentation
      (Scheme.fppfTopology.over S) G.preQuotient.p :=
  Functor.IsFibered.InGroupoids.Stackification.presentation
    (Scheme.fppfTopology.over S) G.preQuotient.p

/-- The comparison of `stackificationPresentation G` is a stackification of `[U /ₚ R]`. -/
theorem stackificationPresentation_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S)
      G.stackificationPresentation.comparison := sorry

/-- The quotient stack `[U / R]` associated to a groupoid in algebraic spaces, obtained by
stackifying `[U /ₚ R]`. -/
def quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    GroupoidsOver S :=
  G.stackificationPresentation.target.toGroupoids

/-- The quotient stack is the target of the selected stackification of `[U /ₚ R]`. -/
theorem quotientStack_spec {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.quotientStack = G.stackificationPresentation.target.toGroupoids := sorry

/-- The quotient stack `[U / R]` is a stack in groupoids on the big fppf site of `S`. -/
instance instIsStackInGroupoids_quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    IsStack.InGroupoids (Scheme.fppfTopology.over S) G.quotientStack.p :=
  StackOver.Groupoids.isStack G.stackificationPresentation.target

/-- The stackification comparison `1`-morphism `[U /ₚ R] ⟶ [U / R]`. -/
def stackificationHom {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : G.preQuotient ⟶ G.quotientStack :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    G.stackificationPresentation.comparison.toBasedFunctor

/-- `stackificationHom` is a stackification of `[U /ₚ R]`. -/
theorem stackificationHom_isStackification {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids.Hom.IsStackification
      (Scheme.fppfTopology.over S) G.stackificationHom := sorry

/-- The functor on total categories sending a `T`-valued point of `U` to the corresponding
object of `[U /ₚ R]`. -/
def atlasToPreQuotientFunctor {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    G.U.left.toGroupoids.total ⥤ G.preQuotient.total where
  obj x :=
    { base := x.unop.fst.unop
      fiber := x.unop.snd }
  map {x y} f :=
    { base := f.unop.val.unop
      fiber :=
        FunctorPointHom.ofArrow
          (G.e.left.app (op x.unop.fst.unop) x.unop.snd) sorry sorry }
  map_id := sorry
  map_comp := sorry

/-- The base of `atlasToPreQuotientFunctor G x` is the scheme underlying the point `x`. -/
theorem atlasToPreQuotientFunctor_base {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (x : G.U.left.toGroupoids.total) :
    (G.atlasToPreQuotientFunctor.obj x).base = x.unop.fst.unop := sorry

/-- The canonical `1`-morphism `𝒮_U ⟶ [U /ₚ R]` sending objects of `U` to objects of the
prestack. -/
def atlasToPreQuotient {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) : G.U.left.toGroupoids ⟶ G.preQuotient :=
  FiberedCategoryOver.Groupoids.ofBasedFunctor
    (BasedFunctor.ofFunctor G.atlasToPreQuotientFunctor sorry)

/-- The atlas `1`-morphism `𝒮_U ⟶ [U / R]`. -/
def atlas {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.U.left.toGroupoids ⟶ G.quotientStack :=
  G.atlasToPreQuotient ≫ G.stackificationHom

/-- The atlas factors as the object inclusion into `[U /ₚ R]` followed by stackification. -/
theorem atlas_eq {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    G.atlas = G.atlasToPreQuotient ≫ G.stackificationHom := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
