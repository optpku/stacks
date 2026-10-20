module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.StructureMap

/-!
# Invariant morphisms from quotient stacks

An invariant morphism from the object space of a groupoid to an algebraic space
induces morphisms from its point prestack and its fppf quotient stack.
-/

@[expose] public section

-- Exposed constructions reference private compatibility laws and the selected lift.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.CategoryOfElements Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- Fibre compatibility for a co-Grothendieck arrow after postcomposition by `h`. -/
private theorem prestackToSpace_map_w {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') (hh : G.s.left ≫ h = G.t.left ≫ h)
    {x y : (preQuotient G).total} (f : x ⟶ y) :
    B'.functorOfPoints.map f.base.op (yonedaEquiv (y.fiber ≫ h)) =
      yonedaEquiv (x.fiber ≫ h) := sorry

/-- The arrow formula for an invariant morphism preserves identity arrows. -/
private theorem prestackToSpace_map_id {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B')
    (hh : G.s.left ≫ h = G.t.left ≫ h)
    (x : (preQuotient G).total) :
    let map := fun {x y : (preQuotient G).total} (f : x ⟶ y) ↦
      (homMk ⟨op y.base, yonedaEquiv (y.fiber ≫ h)⟩
        ⟨op x.base, yonedaEquiv (x.fiber ≫ h)⟩ f.base.op
        (prestackToSpace_map_w G h hh f)).op
    map (𝟙 x) = 𝟙 (op ⟨op x.base, yonedaEquiv (x.fiber ≫ h)⟩ : (stackInSets B').total) := sorry

/-- The arrow formula for an invariant morphism preserves composition. -/
private theorem prestackToSpace_map_comp {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B')
    (hh : G.s.left ≫ h = G.t.left ≫ h)
    {x y z : (preQuotient G).total} (f : x ⟶ y) (k : y ⟶ z) :
    let map := fun {x y : (preQuotient G).total} (f : x ⟶ y) ↦
      (homMk ⟨op y.base, yonedaEquiv (y.fiber ≫ h)⟩
        ⟨op x.base, yonedaEquiv (x.fiber ≫ h)⟩ f.base.op
        (prestackToSpace_map_w G h hh f)).op
    map (f ≫ k) = map f ≫ map k := sorry

/-- The total functor `[U/_p R] ⟶ 𝒮_{B'}` sending a point of `U` to its image under `h`. -/
def prestackToSpaceFunctor {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') (hh : G.s.left ≫ h = G.t.left ≫ h) :
    (preQuotient G).total ⥤ (stackInSets B').total where
  obj x := op ⟨op x.base, yonedaEquiv (x.fiber ≫ h)⟩
  map {x y} f :=
    (homMk ⟨op y.base, yonedaEquiv (y.fiber ≫ h)⟩
        ⟨op x.base, yonedaEquiv (x.fiber ≫ h)⟩ f.base.op
        (prestackToSpace_map_w G h hh f)).op
  map_id := prestackToSpace_map_id G h hh
  map_comp := prestackToSpace_map_comp G h hh

/-- Compatibility of `prestackToSpaceFunctor` with the projections. -/
private theorem prestackToSpace_w {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') (hh : G.s.left ≫ h = G.t.left ≫ h) :
    prestackToSpaceFunctor G h hh ⋙ (stackInSets B').p = (preQuotient G).p := sorry

/-- The cartesian `1`-morphism `[U/_p R] ⟶ 𝒮_{B'}` induced by an invariant morphism `U ⟶ B'`. -/
def prestackToSpace {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') (hh : G.s.left ≫ h = G.t.left ≫ h) :
    CartesianBasedFunctor (preQuotient G).p (stackInSets B').p :=
  CartesianBasedFunctor.ofTargetInGroupoids
    (BasedFunctor.ofFunctor (prestackToSpaceFunctor G h hh) (prestackToSpace_w G h hh))

/-- The selected stackification lift of `prestackToSpace` through `[U/_p R] ⟶ [U/R]`. -/
private def fppfToSpaceLift {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') (hh : G.s.left ≫ h = G.t.left ≫ h) :
    CartesianBasedFunctor.IsStackification.LiftChoice
      (i := (fppfQuotientStackPresentation G).comparison) (prestackToSpace G h hh) :=
  CartesianBasedFunctor.IsStackification.liftChoice
    (fppfQuotientStackPresentation G).isStackification (prestackToSpace G h hh)

/-- The cartesian `1`-morphism `[U/R] ⟶ 𝒮_{B'}` obtained by lifting `prestackToSpace`. -/
def fppfToSpace {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B') (hh : G.s.left ≫ h = G.t.left ≫ h) :
    CartesianBasedFunctor (fppfQuotientStack G).p (stackInSets B').p :=
  (fppfToSpaceLift G h hh).lift

/-- The quotient morphism induced by an invariant morphism restricts along the
stackification comparison to the corresponding prestack morphism. -/
def fppfToSpace_comp {S : Scheme.{u}} {B B' : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h : G.U.left ⟶ B')
    (hh : G.s.left ≫ h = G.t.left ≫ h) :
    (fppfQuotientStackPresentation G).comparison.comp (fppfToSpace G h hh) ≅
      prestackToSpace G h hh :=
  (fppfToSpaceLift G h hh).comparison

end AlgebraicGeometry.GroupoidAlgebraicSpace
