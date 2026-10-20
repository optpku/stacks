/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.InducedTopology
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.SetTheory.Cardinal.Basic
public import ReasLib.AlgebraicGeometry.FormalScheme.Scheme
public import ReasLib.AlgebraicGeometry.Scheme.SmallBoundClosed
public import ReasLib.AlgebraicGeometry.FormalSpectrum.WeaklyAdmissible

@[expose] public section

universe u

noncomputable section

open CategoryTheory Opposite TopCat Topology TopologicalSpace
open TopologicalRing
open scoped Cardinal

namespace AlgebraicGeometry.McQuillan

/-- A locally topologically ringed space is locally weakly affine if every point has
an open neighbourhood isomorphic to the formal spectrum of a weakly admissible ring. -/
def IsLocallyWeaklyAffine : ObjectProperty LocallyTopologicallyRingedSpaceCat.{u} :=
  fun X ↦ ∀ x : X.carrier,
    ∃ (U : OpenNhds x) (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A),
      Nonempty (X.restrict U.isOpenEmbedding ≅ spf A hA)

/-- Weak formal schemes are the full subcategory of locally weakly affine
locally topologically ringed spaces. -/
abbrev FormalScheme := IsLocallyWeaklyAffine.{u}.FullSubcategory

namespace FormalScheme

/-- The underlying locally topologically ringed space of a weak formal scheme. -/
def toLocallyTopologicallyRingedSpace (X : FormalScheme.{u}) :
    LocallyTopologicallyRingedSpaceCat.{u} := X.obj

/-- The underlying sheafed space of a weak formal scheme. -/
def toSheafedSpace (X : FormalScheme.{u}) : SheafedSpace TopCommRingCat.{u} :=
  X.toLocallyTopologicallyRingedSpace.toSheafedSpace

/-- The underlying presheafed space of a weak formal scheme. -/
def toPresheafedSpace (X : FormalScheme.{u}) : PresheafedSpace TopCommRingCat.{u} :=
  X.toSheafedSpace.toPresheafedSpace

/-- The topological space underlying a weak formal scheme. -/
def carrier (X : FormalScheme.{u}) : TopCat.{u} := X.toSheafedSpace.carrier

/-- The presheaf of topological rings on a weak formal scheme. -/
def presheaf (X : FormalScheme.{u}) : X.carrier.Presheaf TopCommRingCat.{u} :=
  X.toSheafedSpace.presheaf

/-- The structure presheaf of a weak formal scheme is a sheaf. -/
theorem IsSheaf (X : FormalScheme.{u}) : X.presheaf.IsSheaf := X.toSheafedSpace.IsSheaf

/-- Every point of a weak formal scheme has a weakly affine neighbourhood. -/
theorem local_affine (X : FormalScheme.{u}) : IsLocallyWeaklyAffine X.obj := X.property

/-- A weak formal spectrum on any homeomorphic presentation is locally weakly affine. -/
theorem spfOnSpace_local_affine (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A)
    {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u)) :
    IsLocallyWeaklyAffine (spfOnSpace A hA e) := sorry

/-- A weak formal spectrum on a specified homeomorphic space, as a weak formal scheme. -/
def ofSpfOnSpace (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A)
    {T : Type u} [TopologicalSpace T]
    (e : T ≃ₜ AlgebraicGeometry.FormalSpectrum.OpenPrime (A : Type u)) : FormalScheme.{u} :=
  ⟨spfOnSpace A hA e, spfOnSpace_local_affine A hA e⟩

/-- Morphisms of weak formal schemes are the morphisms in their full subcategory. -/
abbrev Hom (X Y : FormalScheme.{u}) := X ⟶ Y

/-- The underlying local morphism of a weak formal-scheme morphism. -/
def Hom.toLTRSHom {X Y : FormalScheme.{u}} (f : Hom X Y) :
    LocallyTopologicallyRingedSpaceCat.Hom
      X.toLocallyTopologicallyRingedSpace Y.toLocallyTopologicallyRingedSpace := f.hom

/-- The identity morphism of a weak formal scheme. -/
def id (X : FormalScheme.{u}) : Hom X X := 𝟙 X

/-- Composition of weak formal-scheme morphisms. -/
def comp {X Y Z : FormalScheme.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z := f ≫ g

/-- An admissible formal scheme is locally isomorphic to weak formal spectra. -/
theorem ofFormalScheme_local_affine (X : AlgebraicGeometry.FormalScheme.{u}) :
    IsLocallyWeaklyAffine X.toLocallyTopologicallyRingedSpace := sorry

/-- The comparison from admissible to weak formal schemes retains the underlying
locally topologically ringed spaces and local morphisms. -/
def ofFormalScheme : AlgebraicGeometry.FormalScheme.{u} ⥤ FormalScheme.{u} :=
  IsLocallyWeaklyAffine.lift AlgebraicGeometry.FormalScheme.forgetToLTRS
    ofFormalScheme_local_affine

/-- The comparison from admissible formal schemes preserves the underlying space and sheaf. -/
theorem ofFormalScheme_obj (X : AlgebraicGeometry.FormalScheme.{u}) :
    (ofFormalScheme.obj X).toLocallyTopologicallyRingedSpace =
      X.toLocallyTopologicallyRingedSpace := rfl

/-- Schemes map to weak formal schemes via their pseudo-discrete structure sheaves. -/
def ofScheme : Scheme.{u} ⥤ FormalScheme.{u} := Scheme.toFormalScheme ⋙ ofFormalScheme

/-- The scheme comparison is the composite through admissible formal schemes. -/
theorem ofScheme_eq : ofScheme.{u} = Scheme.toFormalScheme ⋙ ofFormalScheme := rfl

/-- An open of a McQuillan formal scheme is a formal affine open if the restricted
locally topologically ringed space is isomorphic to `spf` of a weakly admissible
topological ring. -/
def IsAffineOpen {X : FormalScheme.{u}} (U : Opens X.carrier) : Prop :=
  ∃ (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A),
    Nonempty (X.toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA)

/-- The set of formal affine opens of a McQuillan formal scheme. -/
def affineOpens (X : FormalScheme.{u}) : Set (Opens X.carrier) :=
  {U | IsAffineOpen U}

/-- Membership in `affineOpens` is equivalent to being a formal affine open. -/
theorem mem_affineOpens {X : FormalScheme.{u}} {U : Opens X.carrier} :
    U ∈ X.affineOpens ↔ IsAffineOpen U :=
  Iff.rfl

/-- A formal affine open is isomorphic in LTRS to `spf` of a weakly admissible
topological ring. -/
theorem isAffineOpen_iff {X : FormalScheme.{u}} {U : Opens X.carrier} :
    IsAffineOpen U ↔
      ∃ (A : TopCommRingCat.{u}) (hA : IsWeaklyAdmissibleRing A),
        Nonempty
          (X.toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA) :=
  Iff.rfl

/-- The cardinal size of a weak formal scheme,
`ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U))`. -/
noncomputable def size (X : FormalScheme.{u}) : Cardinal.{u} :=
  ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U))

/-- The size is the supremum of the countable cardinal, the affine-open cardinality,
and the cardinalities of affine section rings. -/
theorem size_eq (X : FormalScheme.{u}) :
    X.size = ℵ₀ ⊔ #X.affineOpens ⊔ ⨆ U : X.affineOpens, #(X.presheaf.obj (op U)) :=
  rfl

/-- The functor of points of McQuillan formal schemes, restricted to the full
subcategory selected by an object property `P` of schemes: `h_X(S)` is the type of
morphisms of McQuillan formal schemes from the comparison image of `S` to `X`. -/
def functorOfPoints (P : ObjectProperty Scheme.{u}) :
    FormalScheme.{u} ⥤ (P.FullSubcategory)ᵒᵖ ⥤ Type u :=
  yoneda ⋙
    (Functor.whiskeringLeft (P.FullSubcategory)ᵒᵖ (FormalScheme.{u})ᵒᵖ (Type u)).obj
      (P.ι ⋙ ofScheme).op

/-- On objects, the restricted functor of points is the Hom-type
`ofScheme.obj (P.ι.obj S.unop) ⟶ X`. -/
theorem functorOfPoints_obj (P : ObjectProperty Scheme.{u}) (X : FormalScheme.{u})
    (S : (P.FullSubcategory)ᵒᵖ) :
    ((functorOfPoints P).obj X).obj S = (ofScheme.obj (P.ι.obj S.unop) ⟶ X) :=
  rfl

/-- Restricting the functor of points gives a bijection on morphisms when the source
size is bounded by a scheme in the chosen category of test schemes. -/
theorem functorOfPoints_map_bijective {P : ObjectProperty Scheme.{u}}
    (hP : Scheme.IsSmallBoundClosed P) {X Y : FormalScheme.{u}}
    (hX : ∃ S, P S ∧ X.size ≤ S.size) :
    Function.Bijective
      ((functorOfPoints P).map :
        (X ⟶ Y) → ((functorOfPoints P).obj X ⟶ (functorOfPoints P).obj Y)) :=
  sorry

/-- The restricted functor of points of a weak formal scheme is a sheaf for the
restricted fpqc topology. -/
theorem functorOfPoints_isSheaf_fpqc {P : ObjectProperty Scheme.{u}}
    (hP : Scheme.IsSmallBoundClosed P) (X : FormalScheme.{u}) :
    Presheaf.IsSheaf (P.ι.restrictedTopology Scheme.fpqcTopology)
      ((functorOfPoints P).obj X) :=
  sorry

end FormalScheme

end AlgebraicGeometry.McQuillan
