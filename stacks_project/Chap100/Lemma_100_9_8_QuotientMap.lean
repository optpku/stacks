module

public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.Composition
public import ReasLib.CategoryTheory.Fibered.CoGrothendieck.Presheaf
public import ReasLib.CategoryTheory.Fibered.InGroupoids.Cartesian
public import ReasLib.CategoryTheory.Fibered.Stack.Stackification
public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap94.Theorem_94_17_3
public import stacks_project.Chap100.Lemma_100_9_8_Restrict
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Immersion

/-!
# Quotient-stack morphisms induced by morphisms of groupoids

A morphism `f : Hom G H` of groupoids in algebraic spaces induces a morphism of
Chap94 prestacks `[U /ₚ R] ⟶ [U' /ₚ R']`. Composing with stackification of the
target and lifting through stackification of the source produces the canonical
1-morphism `[f] : [U / R] ⟶ [U' / R']`. Restricting along a subspace yields
`restrictQuotientHom G Z : [Z / R_Z] ⟶ [U / R]`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.GroupoidAlgebraicSpace
open FiberedCategoryOver.Groupoids
open Functor Opposite
open scoped Bicategory Pseudofunctor.StrongTrans

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

namespace Hom

/- The functor of Chap94 groupoid-valued points induced by a morphism of groupoids. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.presheafMap : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {G H : GroupoidAlgebraicSpace B}
    (f : Hom G H) ,
    G.groupoidPresheaf ⟶ H.groupoidPresheaf)

/- On objects, `presheafMap` applies the object map of `f` to functor-of-points. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.presheafMap_obj : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) (T : (Over S)ᵒᵖ)
    (x : G.U.left.functorOfPoints.obj T) ,
    ((presheafMap f).app T).obj x = f.obj.left.app T x)

/- The strong transformation of co-Grothendieck pseudofunctors associated to `presheafMap`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.presheafStrongTrans : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) ,
    (G.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor' ⟶
      (H.groupoidPresheaf ⋙ Grpd.forgetToCat).toPseudofunctor')

/- The total functor of co-Grothendieck projections induced by `presheafMap`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.preQuotientMapFunctor : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) ,
    G.preQuotient.total ⥤ H.preQuotient.total)

/- The 1-morphism `[U /ₚ R] ⟶ [U' /ₚ R']` of prestacks induced by a morphism of
groupoids. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.preQuotientMap : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) ,
    G.preQuotient ⟶ H.preQuotient)

/- The cartesian based functor underlying `preQuotientMap`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.preQuotientMapCartesian : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) ,
    CartesianBasedFunctor G.preQuotient.p H.preQuotient.p)

/- The composite `[U /ₚ R] ⟶ [U' / R']` of `preQuotientMapCartesian` with stackification of
the target. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.preQuotientToQuotient : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) ,
    CartesianBasedFunctor G.preQuotient.p H.quotientStack.p)

/- The selected stackification lift of `preQuotientToQuotient` through `[U /ₚ R] ⟶ [U / R]`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.smallQuotientStackLift : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) ,
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := G.stackificationPresentation.comparison) (preQuotientToQuotient f))

/- The canonical 1-morphism `[f] : [U / R] ⟶ [U' / R']` of Chap94 quotient stacks induced by
a morphism of groupoids in algebraic spaces. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackHom : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) ,
    G.quotientStack ⟶ H.quotientStack)

/- `quotientStackHom` is the groupoid-fibred morphism associated to the selected
stackification lift of `preQuotientToQuotient`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackHom_eq : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) ,
    toBasedFunctor (quotientStackHom f) =
      CartesianBasedFunctor.toBasedFunctor (smallQuotientStackLift f).lift)

/- The characterizing invertible 2-cell of the stackification universal property:
precomposing `[f]` with `[U /ₚ R] ⟶ [U / R]` recovers `preQuotientToQuotient`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.Hom.quotientStackHom_comp : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    {G H : GroupoidAlgebraicSpace B} (f : Hom G H) ,
    (CartesianBasedFunctor.precomp H.quotientStack.p
          G.stackificationPresentation.comparison).obj
        (smallQuotientStackLift f).lift ≅ preQuotientToQuotient f)

end Hom

/- The morphism `[Z / R_Z] ⟶ [U / R]` of quotient stacks induced by restriction to a
locally closed subspace. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictQuotientHom : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    (restrict G Z).quotientStack ⟶ G.quotientStack)

/- `restrictQuotientHom` is `quotientStackHom` of `restrictHom`. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.restrictQuotientHom_eq : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (Z : LocallyClosedSubspace G.U.left) ,
    restrictQuotientHom G Z = Hom.quotientStackHom (restrictHom G Z))

/- The quotient stack of the restriction of a smooth groupoid to an invariant locally closed
subspace is an algebraic stack. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.algebraicStack_restrictQuotient : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (Z : LocallyClosedSubspace G.U.left)
    (hZ : G.IsLocallyClosedInvariant Z) ,
    AlgebraicStack (restrict G Z).quotientStack)

/- The quotient stack of the restriction of a smooth groupoid to an invariant open subspace
is an algebraic stack. -/
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.algebraicStack_restrictQuotient_open : ∀ {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] (W : OpenSubspace G.U.left)
    (hW : G.IsOpenInvariant W) ,
    AlgebraicStack (restrict G W.toLocallyClosed).quotientStack)

end AlgebraicGeometry.GroupoidAlgebraicSpace
