module

public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sets.Opens
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiSite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Correspondence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Points

/-! # The small Zariski site and the opens of the point space -/

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

/-- The structural morphism of the site object of an open subspace is its inclusion. -/
theorem toSite_hom {S : Scheme.{u}} {X : AlgebraicSpace S} (U : OpenSubspace X) :
    U.toSite.hom = U.ι :=
  rfl

/-- The open subspace determined by an object of the small Zariski site. -/
def ofSite {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallZariskiSite X) :
    OpenSubspace X where
  X := U.left
  ι := U.hom
  isOpenImmersion := U.prop

/-- The inclusion of the open subspace of a site object is its structural morphism. -/
theorem ofSite_ι {S : Scheme.{u}} {X : AlgebraicSpace S} (U : smallZariskiSite X) :
    (ofSite U).ι = U.hom :=
  rfl

end OpenSubspace

/-- The functor from the small Zariski site to opens of the point space, sending an open
immersion to the image of its map on points. -/
def smallZariskiRangeFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) :
    smallZariskiSite X ⥤ Opens (Points X) where
  obj U := OpenSubspace.pointsOpens (OpenSubspace.ofSite U)
  map {U V} f := homOfLE
    ((OpenSubspace.pointsSet_subset_iff (OpenSubspace.ofSite U)
      (OpenSubspace.ofSite V)).mpr ⟨f.left, MorphismProperty.Over.w f⟩)
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The image of a site object is the open point set of its associated open subspace. -/
theorem smallZariskiRangeFunctor_obj {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallZariskiSite X) :
    (smallZariskiRangeFunctor X).obj U = OpenSubspace.pointsOpens (OpenSubspace.ofSite U) :=
  rfl

/-- The underlying set of the image of a site object is the range of its map on points. -/
theorem smallZariskiRangeFunctor_obj_carrier {S : Scheme.{u}} {X : AlgebraicSpace S}
    (U : smallZariskiSite X) :
    ((smallZariskiRangeFunctor X).obj U).carrier = Set.range (Points.map U.hom) :=
  rfl

/-- A morphism in the small Zariski site induces an inclusion of point images. -/
theorem smallZariskiRangeFunctor_map_carrier_subset {S : Scheme.{u}} {X : AlgebraicSpace S}
    {U V : smallZariskiSite X} (f : U ⟶ V) :
    ((smallZariskiRangeFunctor X).obj U).carrier ⊆
      ((smallZariskiRangeFunctor X).obj V).carrier :=
  leOfHom ((smallZariskiRangeFunctor X).map f)

/-- A displayed family covers a site object if and only if the point images of its sources
cover the point image of the target. -/
theorem ofArrows_mem_smallZariskiPrecoverage_iff_iUnion_points {S : Scheme.{u}}
    {X : AlgebraicSpace S} {I : Type u} [Small.{u} I] {U : smallZariskiSite X}
    {V : I → smallZariskiSite X} {f : ∀ i, V i ⟶ U} :
    Presieve.ofArrows V f ∈ smallZariskiPrecoverage X U ↔
      ⋃ i, Set.range (Points.map (V i).hom) = Set.range (Points.map U.hom) :=
  sorry

/-- The canonical point-image functor from the small Zariski site to opens is an equivalence. -/
instance smallZariskiRangeFunctor_isEquivalence {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallZariskiRangeFunctor X).IsEquivalence :=
  sorry

/-- The canonical point-image functor is a dense subsite for the small Zariski topology and
the canonical topology on opens of the point space. -/
instance smallZariskiRangeFunctor_isDenseSubsite {S : Scheme.{u}} (X : AlgebraicSpace S) :
    (smallZariskiRangeFunctor X).IsDenseSubsite (smallZariskiTopology X)
      (Opens.grothendieckTopology (Points X)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
