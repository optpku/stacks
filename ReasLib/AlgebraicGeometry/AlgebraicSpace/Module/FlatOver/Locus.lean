module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology

/-!
# Openness of the relative flat locus on algebraic spaces

For a locally finitely presented morphism of algebraic spaces, the relative flat
locus of a finitely presented module sheaf is open in the space of points.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The locus of points of `X` at which a module sheaf `F` is flat over `Y`. -/
def flatOverLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules)
    (f : X ⟶ Y) : Set (Points X) :=
  {x | flatOverAt F f x}

/-- Membership in `flatOverLocus F f` is pointwise relative flatness of `F` over `Y`. -/
theorem mem_flatOverLocus {S : Scheme.{u}} {X Y : AlgebraicSpace S} (F : X.Modules)
    (f : X ⟶ Y) (x : Points X) :
    x ∈ flatOverLocus F f ↔ flatOverAt F f x :=
  Iff.rfl

/-- For a locally finitely presented morphism of algebraic spaces, the locus where a
finitely presented module sheaf on the source is flat over the target is open. -/
@[stacks 05WV]
theorem isOpen_flatOverAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation] :
    IsOpen (flatOverLocus F f) :=
  sorry

/-- In a cartesian square of algebraic spaces with flat base morphism and locally finitely
presented vertical morphism, the relative flat locus of a pulled-back finitely presented
module is the inverse image of its original relative flat locus. -/
@[stacks 05WW]
theorem flatOverLocus_eq_preimage {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (hcart : IsPullback g' f' f g) [Flat g] [LocallyOfFinitePresentation f]
    (F : X.Modules) [F.IsFinitePresentation] :
    flatOverLocus ((pullback g').obj F) f' = Points.map g' ⁻¹' flatOverLocus F f :=
  sorry

/-- A point of `|X'|` lies in the relative-flatness locus of `(pullback g').obj F`
over `Y'` if and only if its image under `Points.map g'` lies in
`flatOverLocus F f`. -/
theorem mem_flatOverLocus_eq_preimage {S : Scheme.{u}}
    {X' X Y' Y : AlgebraicSpace S} (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (g : Y' ⟶ Y) (hcart : IsPullback g' f' f g) [Flat g]
    [LocallyOfFinitePresentation f] (F : X.Modules) [F.IsFinitePresentation]
    (x' : Points X') :
    x' ∈ flatOverLocus ((pullback g').obj F) f' ↔
      Points.map g' x' ∈ flatOverLocus F f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
