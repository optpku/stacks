module

public import Mathlib.Topology.Sets.Opens
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Definition_65_9_3_Presentation
public import stacks_project.Chap66.Lemma_66_4_6_Topology

/-!
# Opens of points of an algebraic space

An open subspace `U ⊂ X` determines the subset `|U| ⊆ |X|` as the image of
`Points.map U.ι`. This image is open in the canonical topology of Lemma 66.4.6,
and every open of `|X|` arises uniquely up to unique lift from an open subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u w

namespace AlgebraicGeometry.AlgebraicSpace

namespace Presentation

/-- The topology on `|X|` coinduced by a presentation atlas along `Points.mapOfOver`. -/
@[reducible]
def quotientTopology {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X) :
    TopologicalSpace (Points X) :=
  TopologicalSpace.coinduced (Points.mapOfOver P.atlas) inferInstance

/-- `quotientTopology P` is the topology coinduced by `Points.mapOfOver P.atlas`. -/
theorem quotientTopology_def {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X) :
    P.quotientTopology =
      TopologicalSpace.coinduced (Points.mapOfOver P.atlas) inferInstance :=
  sorry

/-- The coinduced topology of a presentation atlas equals the canonical topology on `|X|`. -/
theorem quotientTopology_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X) :
    P.quotientTopology = instTopologicalSpacePoints X :=
  sorry

/-- A presentation atlas is an open quotient map onto `|X|` with its canonical topology. -/
theorem isOpenQuotientMap_atlas {S : Scheme.{u}} {X : AlgebraicSpace S} (P : Presentation X) :
    IsOpenQuotientMap (Points.mapOfOver P.atlas) :=
  sorry

end Presentation

namespace OpenSubspace

/-- The underlying set of points of an open subspace, as the image of `|U| → |X|`. -/
def pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) : Set (Points X) :=
  Set.range (Points.map U.ι)

/-- `pointsSet U` is the range of `Points.map U.ι`. -/
theorem pointsSet_eq {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    U.pointsSet = Set.range (Points.map U.ι) :=
  sorry

/-- A point of `|X|` lies in `pointsSet U` if and only if it is the image of a point of `|U|`. -/
theorem mem_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X)
    {x : Points X} :
    x ∈ U.pointsSet ↔ ∃ y : Points U.X, Points.map U.ι y = x :=
  sorry

/-- The identity open subspace occupies all of `|X|`. -/
theorem pointsSet_id {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (OpenSubspace.id X).pointsSet = Set.univ :=
  sorry

/-- The image `|U| ⊆ |X|` is open in the canonical topology on `|X|`. -/
theorem isOpen_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    IsOpen U.pointsSet :=
  sorry

/-- The image `|U| ⊆ |X|` as an open of the topological space `|X|`. -/
def pointsOpens {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    Opens (Points X) :=
  Opens.mk U.pointsSet (isOpen_pointsSet U)

/-- The carrier of `pointsOpens U` is `U.pointsSet`. -/
theorem pointsOpens_carrier {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    U.pointsOpens.carrier = U.pointsSet :=
  sorry

/-- Inclusion of underlying point-sets of open subspaces is equivalent to the existence of a
morphism over `X`. -/
theorem pointsSet_subset_iff {S : Scheme.{u}} {X : AlgebraicSpace S} (U V : OpenSubspace X) :
    U.pointsSet ⊆ V.pointsSet ↔ ∃ f : U.X ⟶ V.X, f ≫ V.ι = U.ι :=
  sorry

/-- Every open of `|X|` is the point-set of an open subspace of `X`, unique up to unique lift. -/
theorem exists_of_isOpen {S : Scheme.{u}} {X : AlgebraicSpace S}
    (W : Set (Points X)) (hW : IsOpen W) :
    ∃ U : OpenSubspace X, U.pointsSet = W ∧
      ∀ V : OpenSubspace X, V.pointsSet = W → ∃! f : V.X ⟶ U.X, f ≫ U.ι = V.ι :=
  sorry

end OpenSubspace

/-- A family of open immersions is a Zariski covering if and only if the images of points
cover `|X|`. -/
theorem isZariskiCover_iff_iUnion_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : Type w} [Small.{u} I] (Fi : I → AlgebraicSpace S) (ι : ∀ i, Fi i ⟶ X)
    [∀ i, IsOpenImmersion (ι i)] :
    IsZariskiCover X Fi ι ↔ ⋃ i, Set.range (Points.map (ι i)) = Set.univ :=
  sorry

namespace ZariskiCover

/-- The images of the members of a Zariski covering cover `|X|`. -/
theorem iUnion_pointsSet {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X) :
    ⋃ i, Set.range (Points.map (𝒰.f i)) = Set.univ :=
  sorry

end ZariskiCover

end AlgebraicGeometry.AlgebraicSpace
