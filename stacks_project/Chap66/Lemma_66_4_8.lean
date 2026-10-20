module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Correspondence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiSite.Opens
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u w

/- Lemma 66.4.8 (1): the rule `X' ↦ |X'|` is an inclusion-preserving bijection between
open subspaces of an algebraic space `X` and opens of the topological space `|X|`. -/
@[stacks 03BZ] #check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.exists_of_isOpen :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : Set (Points X)) (hW : IsOpen W),
    ∃ U : OpenSubspace X, U.pointsSet = W ∧
      ∀ V : OpenSubspace X, V.pointsSet = W → ∃! f : V.X ⟶ U.X, f ≫ U.ι = V.ι)

/- Lemma 66.4.8 (1): inclusion of point sets is equivalent to factorization over `X`. -/
@[stacks 03BZ] #check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.pointsSet_subset_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (U V : OpenSubspace X),
    U.pointsSet ⊆ V.pointsSet ↔ ∃ f : U.X ⟶ V.X, f ≫ V.ι = U.ι)

/- Lemma 66.4.8 (2): a family of open subspaces of `X` is a Zariski covering if and only
if `|X| = ⋃ |Xᵢ|`. -/
@[stacks 03BZ] #check (AlgebraicGeometry.AlgebraicSpace.isZariskiCover_iff_iUnion_pointsSet :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type w} [Small.{u} I]
    (Fi : I → AlgebraicSpace S) (ι : ∀ i, Fi i ⟶ X) [∀ i, IsOpenImmersion (ι i)],
    IsZariskiCover X Fi ι ↔ ⋃ i, Set.range (Points.map (ι i)) = Set.univ)

/- Lemma 66.4.8 (3): the small Zariski site `X_Zar` is canonically identified with the
opens site of `|X|` associated to `Opens.grothendieckTopology`. -/
@[stacks 03BZ] #check (AlgebraicGeometry.AlgebraicSpace.smallZariskiRangeFunctor_isEquivalence :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), (smallZariskiRangeFunctor X).IsEquivalence)

/- Lemma 66.4.8 (3): the canonical comparison also identifies the covering topologies. -/
@[stacks 03BZ] #check (AlgebraicGeometry.AlgebraicSpace.smallZariskiRangeFunctor_isDenseSubsite :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S),
    (smallZariskiRangeFunctor X).IsDenseSubsite (smallZariskiTopology X)
      (Opens.grothendieckTopology (Points X)))
