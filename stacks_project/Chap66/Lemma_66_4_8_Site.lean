/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sets.Opens
public import stacks_project.Chap65.Definition_65_12_6_Site
public import stacks_project.Chap66.Lemma_66_4_8_Opens

/-!
# Small Zariski site versus opens of points

The comparison functor from the small Zariski site of an algebraic space to the
opens of `|X|` sends an open immersion to the image of its map on points. This
exhibits `X_Zar` as a dense subsite of the canonical opens site of `|X|`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace OpenSubspace

/-- The object of the small Zariski site determined by an open subspace. -/
def toSite {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    smallZariskiSite X :=
  MorphismProperty.Over.mk ⊤ U.ι U.isOpenImmersion

/-- The structural morphism of `toSite U` is the inclusion of `U`. -/
theorem toSite_hom {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    U.toSite.hom = U.ι :=
  sorry

/-- The open subspace determined by an object of the small Zariski site. -/
def ofSite {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallZariskiSite X) :
    OpenSubspace X where
  X := U.left
  ι := U.hom
  isOpenImmersion := U.prop

/-- The inclusion of `ofSite U` is the structural morphism of `U`. -/
theorem ofSite_ι {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallZariskiSite X) :
    (ofSite U).ι = U.hom :=
  sorry

end OpenSubspace

/-- The comparison functor `X_Zar ⥤ Opens |X|` sending an open immersion to the image of
its map on points. -/
def smallZariskiRangeFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallZariskiSite X ⥤ Opens (Points X) where
  obj U := OpenSubspace.pointsOpens (OpenSubspace.ofSite U)
  map f := homOfLE sorry
  map_id := sorry
  map_comp := sorry

/-- The object of `smallZariskiRangeFunctor X` at an open immersion is the corresponding
open of `|X|`. -/
theorem smallZariskiRangeFunctor_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallZariskiSite X) :
    (smallZariskiRangeFunctor X).obj U = OpenSubspace.pointsOpens (OpenSubspace.ofSite U) :=
  sorry

/-- The underlying set of `smallZariskiRangeFunctor X` on an open immersion `U ⟶ X` is the
image of `|U| → |X|`. -/
theorem smallZariskiRangeFunctor_obj_carrier {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallZariskiSite X) :
    ((smallZariskiRangeFunctor X).obj U).carrier = Set.range (Points.map U.hom) :=
  sorry

/-- A morphism in the small Zariski site induces an inclusion of images of points. -/
theorem smallZariskiRangeFunctor_map_carrier_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallZariskiSite X} (f : U ⟶ V) :
    ((smallZariskiRangeFunctor X).obj U).carrier ⊆
      ((smallZariskiRangeFunctor X).obj V).carrier :=
  sorry

/-- A displayed family is a covering in the small Zariski precoverage if and only if the
images of points of the sources cover the image of the target. -/
theorem ofArrows_mem_smallZariskiPrecoverage_iff_iUnion_points {S : Scheme.{u}}
    {X : AlgebraicSpace S} {I : Type u} [Small.{u} I] {U : smallZariskiSite X}
    {V : I → smallZariskiSite X} {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ smallZariskiPrecoverage X U ↔
      ⋃ i, Set.range (Points.map (V i).hom) = Set.range (Points.map U.hom) :=
  sorry

/-- The comparison functor identifies the small Zariski site of `X` with the canonical
opens site of `|X|`. -/
instance smallZariskiRangeFunctor_isDenseSubsite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallZariskiRangeFunctor X).IsDenseSubsite (smallZariskiTopology X)
      (Opens.grothendieckTopology (Points X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
