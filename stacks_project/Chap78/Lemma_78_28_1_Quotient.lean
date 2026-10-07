module

public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Yoneda
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.Pushforward.InGroupoids
public import ReasLib.CategoryTheory.Fibered.Stack.InGroupoidsOver.Stackification
public import stacks_project.Chap78.Lemma_78_28_1_InverseImage
public import stacks_project.Chap78.«78_20_0_1_Points»

/-!
# Quotient stacks of groupoids in algebraic spaces

The prestack `[U/_p R]` is the co-Grothendieck projection of the groupoid-valued
points functor. On a contained site this is formed from sheaf-valued points; `[U/R]`
is its stackification. The large-site prestack `u_p[U/_p R]` is the pushforward of
that small-site prestack along `slicePost ι S`. The quotient stack `[f⁻¹U/f⁻¹R]` is
the stackification of the inverse-image groupoid, not of this pushforward.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits
open Functor.IsFibered.InGroupoids.Stackification
open Opposite Pseudofunctor.CoGrothendieck

noncomputable section

universe u uC

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The prestack `[U/_p R]` associated to a groupoid in algebraic spaces, as the co-Grothendieck
projection of the groupoid-valued functor of points. -/
def prestack {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    FiberedCategoryOver.Groupoids (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor (groupoidPresheafProjection G.points)

/-- The projection of `prestack G` is the co-Grothendieck projection of `G.points`. -/
theorem prestack_p {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    (prestack G).p = groupoidPresheafProjection G.points := sorry

/-- The selected stackification presentation of `[U/_p R]` on `(Sch/S)_fppf`. -/
def fppfQuotientStackPresentation {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    Presentation (Scheme.fppfTopology.over S) (groupoidPresheafProjection G.points) :=
  presentation (Scheme.fppfTopology.over S) (groupoidPresheafProjection G.points)

/-- The quotient stack `[U/R]` of a groupoid in algebraic spaces over `B`, as the selected
stackification of `[U/_p R]` on `(Sch/S)_fppf`. -/
def fppfQuotientStack {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    StackOver.Groupoids (Scheme.fppfTopology.over S) :=
  (fppfQuotientStackPresentation G).target

/-- The selected comparison from `[U/_p R]` to `[U/R]` is a stackification. -/
theorem fppfQuotientStack_isStackification {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    CartesianBasedFunctor.IsStackification (Scheme.fppfTopology.over S)
      (fppfQuotientStackPresentation G).comparison := sorry

variable {C : Type uC} [Category.{u} C] (ι : C ⥤ Scheme.{u})
variable (J : GrothendieckTopology C) (S : C)
variable [ι.Full] [ι.Faithful] [J.Subcanonical]
variable [PreservesLimitsOfShape WalkingCospan ι]
variable [(slicePost ι S).IsContinuous (J.over S) (Scheme.fppfTopology.over (ι.obj S))]
variable [HasWeakSheafify (Scheme.fppfTopology.over (ι.obj S)) (Type u)]
variable [∀ P : (Over S)ᵒᵖ ⥤ Type u, (slicePost ι S).op.HasLeftKanExtension P]
variable [PreservesFiniteLimits
  ((slicePost ι S).sheafPullback (Type u) (J.over S)
    (Scheme.fppfTopology.over (ι.obj S)))]
variable [HasPullbacks (Sheaf (J.over S) (Type u))]

variable {ι J S}

/-- A morphism between two sheaf-valued points of a groupoid on a contained site. -/
structure SlicePointHom (G : GroupoidOnSlice ι J S) {T : Over S}
    (x y : G.U.sheaf.obj.obj (op T)) where
  /-- The underlying sheaf-valued arrow. -/
  arrow : G.R.sheaf.obj.obj (op T)
  /-- The arrow has source `x`. -/
  source : (Sheaf.homEquiv G.s).app (op T) arrow = x
  /-- The arrow has target `y`. -/
  target : (Sheaf.homEquiv G.t).app (op T) arrow = y

/-- Composable sheaf-valued arrows have matching source and target after applying `G.s` and
`G.t`, so they lift to the fibre product of source and target. -/
theorem sliceCompArrow_lift_comm {G : GroupoidOnSlice ι J S} {T : Over S}
    {x y z : G.U.sheaf.obj.obj (op T)} (f : SlicePointHom G x y) (g : SlicePointHom G y z) :
    (J.over S).yonedaEquiv.symm g.arrow ≫ G.s =
      (J.over S).yonedaEquiv.symm f.arrow ≫ G.t := sorry

/-- The composite sheaf-valued arrow of two composable points, obtained by lifting to the
fibre product of source and target and applying composition. -/
def sliceCompArrow (G : GroupoidOnSlice ι J S) {T : Over S}
    {x y z : G.U.sheaf.obj.obj (op T)} (f : SlicePointHom G x y) (g : SlicePointHom G y z) :
    G.R.sheaf.obj.obj (op T) :=
  (J.over S).yonedaEquiv
    (pullback.lift ((J.over S).yonedaEquiv.symm g.arrow)
      ((J.over S).yonedaEquiv.symm f.arrow) (sliceCompArrow_lift_comm f g) ≫ G.c)

/-- The explicit groupoid of sheaf-valued `T`-points of a contained-site groupoid. -/
@[reducible]
def slicePointGroupoid (G : GroupoidOnSlice ι J S) (T : Over S) :
    CategoryTheory.Groupoid.{u, u} (G.U.sheaf.obj.obj (op T)) where
  Hom := SlicePointHom G
  id := fun x ↦
    { arrow := (Sheaf.homEquiv G.e).app (op T) x
      source := sorry
      target := sorry }
  comp := fun f g ↦
    { arrow := sliceCompArrow G f g
      source := sorry
      target := sorry }
  id_comp := sorry
  comp_id := sorry
  assoc := sorry
  inv := fun f ↦
    { arrow := (Sheaf.homEquiv G.i).app (op T) f.arrow
      source := sorry
      target := sorry }
  inv_comp := sorry
  comp_inv := sorry

/-- The bundled groupoid of sheaf-valued `T`-points of a contained-site groupoid. -/
def sliceSpacePoints (G : GroupoidOnSlice ι J S) (T : Over S) : Grpd.{u, u} :=
  ⟨G.U.sheaf.obj.obj (op T), slicePointGroupoid G T⟩

variable (ι) (J) (S)

/-- The functor of sheaf-valued points of a groupoid on a contained site. -/
def slicePoints (G : GroupoidOnSlice ι J S) : (Over S)ᵒᵖ ⥤ Grpd.{u, u} where
  obj T := sliceSpacePoints G T.unop
  map f :=
    { obj := fun x ↦ G.U.sheaf.obj.map f x
      map := fun p ↦
        { arrow := G.R.sheaf.obj.map f p.arrow
          source := sorry
          target := sorry }
      map_id := sorry
      map_comp := sorry }
  map_id := sorry
  map_comp := sorry

/-- The prestack `[U/_p R]` of a contained-site groupoid, as the co-Grothendieck projection of
its sheaf-valued points. -/
def slicePrestack (G : GroupoidOnSlice ι J S) :
    FiberedCategoryOver.Groupoids (Over S) :=
  FiberedCategoryOver.Groupoids.ofFunctor (groupoidPresheafProjection (slicePoints ι J S G))

/-- The projection of the contained-site prestack is the co-Grothendieck projection of the
sheaf-valued points functor. -/
theorem slicePrestack_p (G : GroupoidOnSlice ι J S) :
    (slicePrestack ι J S G).p = groupoidPresheafProjection (slicePoints ι J S G) := sorry

/-- The selected stackification presentation of `[U/_p R]` on the contained slice. -/
def sliceQuotientStackPresentation (G : GroupoidOnSlice ι J S) :
    Presentation (J.over S) (groupoidPresheafProjection (slicePoints ι J S G)) :=
  presentation (J.over S) (groupoidPresheafProjection (slicePoints ι J S G))

/-- The quotient stack `[U/R]` of a contained-site groupoid, as the selected stackification of
`[U/_p R]` on `J.over S`. -/
def sliceQuotientStack (G : GroupoidOnSlice ι J S) :
    StackOver.Groupoids (J.over S) :=
  (sliceQuotientStackPresentation ι J S G).target

/-- The selected comparison from the contained-site prestack to `[U/R]` is a stackification. -/
theorem sliceQuotientStack_isStackification (G : GroupoidOnSlice ι J S) :
    CartesianBasedFunctor.IsStackification (J.over S)
      (sliceQuotientStackPresentation ι J S G).comparison := sorry

variable [HasPullbacks (Over S)] [HasEqualizers (Over S)]
variable [PreservesLimitsOfShape WalkingCospan (slicePost ι S)]
variable [PreservesLimitsOfShape WalkingParallelPair (slicePost ι S)]

/-- The canonical groupoid-fibred pushforward choice for the contained-site prestack along
`slicePost ι S`. -/
theorem slicePrestackPushforwardChoice (G : GroupoidOnSlice ι J S) :
    FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice
      (slicePost ι S) (slicePrestack ι J S G) :=
  FiberedCategoryOver.Groupoids.Pushforward.ProjectionChoice.canonical
    (slicePost ι S) (slicePrestack ι J S G)

/-- The large-site prestack `u_p[U/_p R]`, as the pushforward of the contained-site prestack
along `slicePost ι S`. This is an intermediate in the change-of-site comparison; its
stackification is `f⁻¹[U/R]` by Lemma 8.12.11, whereas `[f⁻¹U/_p f⁻¹R]` is `prestack` of
the inverse-image groupoid. -/
def sliceInverseImagePrestack (G : GroupoidOnSlice ι J S) :
    FiberedCategoryOver.Groupoids (Over (ι.obj S)) :=
  FiberedCategoryOver.Groupoids.pushforward (slicePost ι S) (slicePrestack ι J S G)
    (slicePrestackPushforwardChoice ι J S G)

end AlgebraicGeometry.GroupoidAlgebraicSpace
