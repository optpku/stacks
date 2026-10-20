/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.Opens
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Definition_65_13_2_Separation
public import stacks_project.Chap65.Definition_65_9_3_Presentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Correspondence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Points

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

#check (AlgebraicGeometry.AlgebraicSpace.Points.eq_coinduced_mapOfOver :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X)
    (hp : (MorphismProperty.over (@Etale)).presheaf p)
    (hsurj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p),
    instTopologicalSpacePoints X = TopologicalSpace.coinduced (Points.mapOfOver p) inferInstance)

#check (AlgebraicGeometry.AlgebraicSpace.Points.isOpenQuotientMap_mapOfOver :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S} (p : ofOver U ⟶ X)
    (hp : (MorphismProperty.over (@Etale)).presheaf p)
    (hsurj : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p),
    IsOpenQuotientMap (Points.mapOfOver p))

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.exists_of_isOpen :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (W : Set (Points X)) (hW : IsOpen W),
    ∃ U : OpenSubspace X, U.pointsSet = W ∧
      ∀ V : OpenSubspace X, V.pointsSet = W → ∃! f : V.X ⟶ U.X, f ≫ U.ι = V.ι)

#check (AlgebraicGeometry.AlgebraicSpace.OpenSubspace.pointsSet_subset_iff :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (U V : OpenSubspace X),
    U.pointsSet ⊆ V.pointsSet ↔ ∃ f : U.X ⟶ V.X, f ≫ V.ι = U.ι)

#check (AlgebraicGeometry.AlgebraicSpace.isZariskiCover_iff_iUnion_pointsSet :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type w} [Small.{u} I]
    (Fi : I → AlgebraicSpace S) (ι : ∀ i, Fi i ⟶ X) [∀ i, IsOpenImmersion (ι i)],
    IsZariskiCover X Fi ι ↔ ⋃ i, Set.range (Points.map (ι i)) = Set.univ)

#check (AlgebraicGeometry.AlgebraicSpace.ZariskiCover.iUnion_pointsSet :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} (𝒰 : ZariskiCover X),
    ⋃ i, Set.range (Points.map (𝒰.f i)) = Set.univ)

end AlgebraicGeometry.AlgebraicSpace
