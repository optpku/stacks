module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ClosedSubspace.Reduced.Structure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-!
# Reduced closures of points of algebraic spaces

The canonical reduced induced algebraic space structure on the closure of a
point, together with the induced morphisms along maps of algebraic spaces.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PointClosure

/-- The closed subset given by the closure of a singleton point of an algebraic
space. -/
def closedSubset {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    Closeds (Points X) :=
  Closeds.closure ({x} : Set (Points X))

/-- The carrier of the closed subset associated to a point is its singleton
closure. -/
theorem coe_closedSubset {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    (closedSubset x : Set (Points X)) = closure ({x} : Set (Points X)) :=
  sorry

/-- The canonical reduced induced algebraic space structure on the closure of a
point, in the sense of `ClosedSubspaceStructure.reduced`. -/
def reducedStructure {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    ClosedSubspaceStructure (closedSubset x) :=
  ClosedSubspaceStructure.reduced (closedSubset x)

/-- The reduced induced structure on a singleton closure is
`ClosedSubspaceStructure.reduced` of that closed subset. -/
theorem reducedStructure_eq {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) :
    reducedStructure x = ClosedSubspaceStructure.reduced (closedSubset x) :=
  sorry

/-- The algebraic space with the reduced induced structure on the closure of a
point. -/
def space {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    AlgebraicSpace S :=
  (reducedStructure x).space

/-- The reduced point-closure space is the underlying space of
`reducedStructure`. -/
theorem space_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    space x = (reducedStructure x).space :=
  sorry

/-- The canonical closed immersion from the reduced point closure into the
ambient algebraic space. -/
def ι {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) : space x ⟶ X :=
  (reducedStructure x).ι

/-- The range of the canonical immersion is the singleton closure. -/
theorem range_ι {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    Set.range (Points.map (ι x)) = (closedSubset x : Set (Points X)) :=
  sorry

/-- The canonical reduced point-closure algebraic space is reduced. -/
instance instIsReduced_space {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) : IsReduced (space x) :=
  ReducedClosed.Space.space_reduced X (closedSubset x)

/-- The canonical morphism from a reduced point closure is a closed immersion. -/
instance instIsClosedImmersion_ι {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) : IsClosedImmersion (ι x) :=
  (reducedStructure x).subspace.isClosedImmersion

/-- A morphism of algebraic spaces induces a unique morphism of reduced point
closures over the ambient map. -/
theorem existsUnique_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    ∃! φ : space x ⟶ space (Points.map f x),
      φ ≫ ι (Points.map f x) = ι x ≫ f :=
  sorry

/-- The specified composite has sections in the target reduced image:
the domain is reduced and its point image lies in the target point closure.
This is membership of existing sections, rather than selected factorization data. -/
theorem map_range {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) :
    Subfunctor.range (ι x ≫ f) ≤
      (Subfunctor.range (ReducedClosed.AtlasImage.chartMap Y
        (closedSubset (Points.map f x)))).sheafify (Scheme.fppfTopology.over S) := by
  sorry

/-- The canonical morphism retains the sections of the given composite
and attaches their membership in the target reduced image subsheaf. -/
def map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X) :
    space x ⟶ space (Points.map f x) :=
  Subfunctor.lift (ι x ≫ f) (map_range f x)

/-- The map on reduced point closures commutes with the canonical immersions. -/
theorem map_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : map f x ≫ ι (Points.map f x) = ι x ≫ f :=
  sorry

/-- The map on reduced point closures associated to an identity morphism is the
identity, after identifying `Points.map (𝟙 X) x` with `x`. -/
theorem map_id {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    map (𝟙 X) x ≫ eqToHom (congrArg space (Points.map_id x)) = 𝟙 (space x) :=
  sorry

/-- Maps on reduced point closures preserve composition, after identifying
`Points.map (f ≫ g) x` with `Points.map g (Points.map f x)`. -/
theorem map_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y ⟶ Z) (x : Points X) :
    map (f ≫ g) x ≫ eqToHom (congrArg space (Points.map_comp f g x)) =
      map f x ≫ map g (Points.map f x) :=
  sorry

/-- Affine morphisms of algebraic spaces induce affine morphisms of reduced
point closures. -/
instance instAffine_map {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Affine f] (x : Points X) : Affine (map f x) :=
  sorry

/-- The map on reduced point closures with its target indexed by a specified
image point. -/
def mapOfEq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X)
    (y : Points Y) (h : Points.map f x = y) : space x ⟶ space y :=
  map f x ≫ eqToHom (congrArg space h)

/-- An equality-indexed map on reduced point closures commutes with the
canonical immersions. -/
theorem mapOfEq_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) (y : Points Y) (h : Points.map f x = y) :
    mapOfEq f x y h ≫ ι y = ι x ≫ f :=
  sorry

/-- The equality-indexed map associated to an identity morphism is the
identity. -/
theorem mapOfEq_id {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    mapOfEq (𝟙 X) x x (Points.map_id x) = 𝟙 (space x) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PointClosure
