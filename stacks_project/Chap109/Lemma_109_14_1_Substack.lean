/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import stacks_project.Chap67.Lemma_67_17_2_InverseImage
public import stacks_project.Chap99.Situation_99_15_1_Category
public import stacks_project.Chap109.Lemma_109_14_1_SingularLocus

/-!
# The object property of families of curves with isolated singularities

`Curves⁺` is the full subcategory of families of curves whose structure morphism
has isolated singularities. Membership is the source-facing packaging of a
classifying morphism factoring through that open substack.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inclusion of an open subspace is an open immersion. -/
instance instIsOpenImmersion_openSubspace_ι {S : Scheme.{u}}
    {F : AlgebraicSpace S} (U : OpenSubspace F) : IsOpenImmersion U.ι :=
  U.isOpenImmersion

/-- The restriction of a morphism of algebraic spaces to an open of the
target. -/
def restrictTo {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : OpenSubspace Y) : openInverseImage f U.ι ⟶ U.X :=
  openInverseImageTo f U.ι

/-- `restrictTo f U` is the comparison morphism of the open inverse image of
`U` along `f`. -/
theorem restrictTo_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (U : OpenSubspace Y) :
    restrictTo f U = openInverseImageTo f U.ι :=
  sorry

namespace OpenSubspace

/-- The inverse image of an open subspace along a morphism of algebraic
spaces. -/
def inverseImage {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X) : OpenSubspace Y :=
  ofι (openInverseImageι φ U.ι)

/-- The inclusion of `U.inverseImage φ` is `openInverseImageι φ U.ι`. -/
theorem inverseImage_ι {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (U : OpenSubspace X) (φ : Y ⟶ X) :
    (U.inverseImage φ).ι = openInverseImageι φ U.ι :=
  sorry

end OpenSubspace

/-- `U` is a largest open of the target over which the restriction of `f` has
isolated singularities. -/
def IsLargestIsolatedSingularitiesOpen {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (U : OpenSubspace Y) : Prop :=
  ∀ V : OpenSubspace Y,
    IsolatedSingularities (restrictTo f V) ↔
      ∃ χ : V.X ⟶ U.X, χ ≫ U.ι = V.ι

/-- Unfolding of `IsLargestIsolatedSingularitiesOpen`. -/
theorem isLargestIsolatedSingularitiesOpen_iff {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (U : OpenSubspace Y) :
    IsLargestIsolatedSingularitiesOpen f U ↔
      ∀ V : OpenSubspace Y,
        IsolatedSingularities (restrictTo f V) ↔
          ∃ χ : V.X ⟶ U.X, χ ≫ U.ι = V.ι :=
  sorry

namespace Spaces
namespace Curves

/-- The object property of families of curves whose structure morphism has
isolated singularities, corresponding to the open substack Curves⁺. -/
def isolatedSingularities (S : Scheme.{u}) : ObjectProperty (Obj S) :=
  fun P ↦ IsolatedSingularities (hom P)

/-- Membership in `isolatedSingularities` is isolated singularities of the
structure morphism. -/
theorem isolatedSingularities_iff {S : Scheme.{u}} (P : Obj S) :
    isolatedSingularities S P ↔ IsolatedSingularities (hom P) :=
  sorry

/-- The isolated-singularities property of families of curves is closed under
isomorphisms. -/
instance instIsClosedUnderIsomorphisms_isolatedSingularities
    (S : Scheme.{u}) : (isolatedSingularities S).IsClosedUnderIsomorphisms :=
  sorry

/-- The morphism of algebraic spaces over `Spec k` associated to a scheme over
a field. -/
def schemeOverFieldHom {k : Type u} [Field k] (X : SchemeOverField k) :
    ofOver (Over.mk X.hom) ⟶
      ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :=
  ofOverHomMk X.hom (Category.comp_id X.hom)

/-- `schemeOverFieldHom X` is `ofOverHomMk` of the structure morphism of `X`. -/
theorem schemeOverFieldHom_eq {k : Type u} [Field k] (X : SchemeOverField k) :
    schemeOverFieldHom X =
      ofOverHomMk X.hom (Category.comp_id X.hom) :=
  sorry

/-- A proper scheme over a field is fp-flat-proper as a morphism of algebraic
spaces. -/
instance instFpFlatProper_schemeOverFieldHom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom] :
    FpFlatProper (schemeOverFieldHom X) :=
  sorry

/-- A proper scheme of topological Krull dimension at most one over a field has
relative dimension at most one as a morphism of algebraic spaces. -/
theorem relativeDimensionLE_schemeOverFieldHom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    RelativeDimensionLE (schemeOverFieldHom X) 1 :=
  sorry

/-- Package a proper scheme of topological Krull dimension at most one over a
field as a family of curves over `Spec k`. -/
def mkOfSchemeOverField {k : Type u} [Field k] (X : SchemeOverField k)
    [IsProper X.hom] (hdim : topologicalKrullDim X.left ≤ 1) :
    Obj (Spec (CommRingCat.of k)) :=
  @mk (Spec (CommRingCat.of k)) (Over.mk (𝟙 (Spec (CommRingCat.of k))))
    (ofOver (Over.mk X.hom)) (schemeOverFieldHom X)
    (instFpFlatProper_schemeOverFieldHom X)
    (relativeDimensionLE_schemeOverFieldHom X hdim)

/-- The structure morphism of `mkOfSchemeOverField X hdim` is
`schemeOverFieldHom X`. -/
theorem mkOfSchemeOverField_hom {k : Type u} [Field k]
    (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) :
    hom (mkOfSchemeOverField X hdim) = schemeOverFieldHom X :=
  sorry

/-- Openness on the base (o): there is a largest open of the base over which
the restricted family has isolated singularities, and for every morphism of
families the largest such open of the source base is the inverse image of
that open along `ofOverMap (baseMap φ)`. -/
theorem isolatedSingularities_openOnBase {S : Scheme.{u}} (P : Obj S) :
    ∃ U : OpenSubspace (ofOver (base P)),
      IsLargestIsolatedSingularitiesOpen (hom P) U ∧
        ∀ {Q : Obj S} (φ : Q ⟶ P),
          IsLargestIsolatedSingularitiesOpen (hom Q)
            (U.inverseImage (ofOverMap (baseMap φ))) :=
  sorry

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
