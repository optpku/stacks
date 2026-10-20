/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyTopologicallyRingedSpace
public import ReasLib.AlgebraicGeometry.FormalSpectrum.StructureSheaf
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Formal schemes

Formal schemes are locally topologically ringed spaces locally isomorphic to formal spectra
of admissible topological rings. Their morphisms are local morphisms of the underlying spaces.
-/

@[expose] public section

universe u

noncomputable section

open CategoryTheory TopCat Topology TopologicalSpace

namespace AlgebraicGeometry

/-- The formal spectrum of a bundled admissible topological commutative ring. -/
def spf (A : TopCommRingCat.{u}) (hA : TopologicalRing.IsAdmissibleRing A) :
    LocallyTopologicallyRingedSpaceCat.{u} :=
  @FormalSpectrum.spf (A : Type u) inferInstance inferInstance hA

/-- Every point has an open neighbourhood isomorphic to an admissible formal spectrum. -/
def LocallyTopologicallyRingedSpaceCat.IsFormalScheme
    (X : LocallyTopologicallyRingedSpaceCat.{u}) : Prop :=
  ∀ x : X.carrier,
    ∃ (U : OpenNhds x) (A : TopCommRingCat.{u})
      (hA : TopologicalRing.IsAdmissibleRing A),
      Nonempty (X.restrict U.isOpenEmbedding ≅ spf A hA)

/-- The full subcategory of locally topologically ringed spaces locally isomorphic to
admissible formal spectra. -/
def FormalScheme :=
  ObjectProperty.FullSubcategory LocallyTopologicallyRingedSpaceCat.IsFormalScheme.{u}

namespace FormalScheme

/-- The underlying locally topologically ringed space of a formal scheme. -/
def toLocallyTopologicallyRingedSpace (X : FormalScheme.{u}) :
    LocallyTopologicallyRingedSpaceCat.{u} := X.obj

/-- Every point of a formal scheme has an admissible formal affine neighbourhood. -/
theorem local_affine (X : FormalScheme.{u}) :
    ∀ x : X.toLocallyTopologicallyRingedSpace.carrier,
      ∃ (U : OpenNhds x) (A : TopCommRingCat.{u})
        (hA : TopologicalRing.IsAdmissibleRing A),
        Nonempty (X.toLocallyTopologicallyRingedSpace.restrict U.isOpenEmbedding ≅ spf A hA) :=
  X.property

/-- A locally formally affine locally topologically ringed space defines a formal scheme. -/
def ofLocallyTopologicallyRingedSpace (X : LocallyTopologicallyRingedSpaceCat.{u})
    (hX : X.IsFormalScheme) : FormalScheme.{u} := ⟨X, hX⟩

/-- The formal-scheme constructor retains the given space and its local formal affineness. -/
theorem ofLocallyTopologicallyRingedSpace_spec
    (X : LocallyTopologicallyRingedSpaceCat.{u}) (hX : X.IsFormalScheme) :
    (ofLocallyTopologicallyRingedSpace X hX).toLocallyTopologicallyRingedSpace = X ∧
      X.IsFormalScheme := ⟨rfl, hX⟩

/-- The underlying sheafed space of a formal scheme. -/
def toSheafedSpace (X : FormalScheme.{u}) : SheafedSpace TopCommRingCat.{u} :=
  X.toLocallyTopologicallyRingedSpace.toSheafedSpace

/-- The underlying presheafed space of a formal scheme. -/
def toPresheafedSpace (X : FormalScheme.{u}) : PresheafedSpace TopCommRingCat.{u} :=
  X.toSheafedSpace.toPresheafedSpace

/-- The underlying topological space of a formal scheme. -/
def carrier (X : FormalScheme.{u}) : TopCat.{u} := X.toSheafedSpace.carrier

/-- The presheaf of topological commutative rings of a formal scheme. -/
def presheaf (X : FormalScheme.{u}) : X.carrier.Presheaf TopCommRingCat.{u} :=
  X.toSheafedSpace.presheaf

/-- The presheaf of a formal scheme satisfies the sheaf condition. -/
theorem IsSheaf (X : FormalScheme.{u}) : X.presheaf.IsSheaf := X.toSheafedSpace.IsSheaf

/-- The underlying ring stalks of a formal scheme are local rings. -/
@[instance] theorem isLocalRing (X : FormalScheme.{u}) (x : X.carrier) :
    IsLocalRing ((LocallyTopologicallyRingedSpaceCat.ringPresheaf X.toSheafedSpace).stalk x) :=
  X.toLocallyTopologicallyRingedSpace.property x

/-- Morphisms of formal schemes are local morphisms of their underlying sheafed spaces. -/
def Hom (X Y : FormalScheme.{u}) :=
  InducedCategory.Hom (F := ObjectProperty.FullSubcategory.obj) X Y

/-- Formal schemes inherit the canonical full-subcategory category structure. -/
instance instCategory : Category FormalScheme.{u} :=
  { ObjectProperty.FullSubcategory.category
      LocallyTopologicallyRingedSpaceCat.IsFormalScheme with
    Hom := Hom }

/-- The underlying local morphism of a formal-scheme morphism. -/
def Hom.toLTRSHom {X Y : FormalScheme.{u}} (f : Hom X Y) :
    LocallyTopologicallyRingedSpaceCat.Hom
      X.toLocallyTopologicallyRingedSpace Y.toLocallyTopologicallyRingedSpace := f.hom

/-- Any local morphism between the underlying spaces defines a formal-scheme morphism. -/
def Hom.ofLTRSHom {X Y : FormalScheme.{u}}
    (f : LocallyTopologicallyRingedSpaceCat.Hom
      X.toLocallyTopologicallyRingedSpace Y.toLocallyTopologicallyRingedSpace) : Hom X Y :=
  ObjectProperty.homMk f

/-- Constructing a formal-scheme morphism retains its underlying local morphism. -/
theorem Hom.ofLTRSHom_toLTRSHom {X Y : FormalScheme.{u}}
    (f : LocallyTopologicallyRingedSpaceCat.Hom
      X.toLocallyTopologicallyRingedSpace Y.toLocallyTopologicallyRingedSpace) :
    (Hom.ofLTRSHom f).toLTRSHom = f := rfl

/-- Reconstructing a formal-scheme morphism from its underlying local morphism recovers it. -/
theorem Hom.toLTRSHom_ofLTRSHom {X Y : FormalScheme.{u}} (f : Hom X Y) :
    Hom.ofLTRSHom f.toLTRSHom = f := rfl

/-- The identity formal-scheme morphism. -/
def id (X : FormalScheme.{u}) : Hom X X := 𝟙 X

/-- Composition of formal-scheme morphisms composes their supplied underlying morphisms. -/
def comp {X Y Z : FormalScheme.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  CategoryStruct.comp (X := X) (Y := Y) (Z := Z) f g

/-- Left identity for composition of formal-scheme morphisms. -/
theorem id_comp {X Y : FormalScheme.{u}} (f : Hom X Y) : comp (id X) f = f := sorry

/-- Right identity for composition of formal-scheme morphisms. -/
theorem comp_id {X Y : FormalScheme.{u}} (f : Hom X Y) : comp f (id Y) = f := sorry

/-- Associativity of composition of formal-scheme morphisms. -/
theorem assoc {W X Y Z : FormalScheme.{u}} (f : Hom W X) (g : Hom X Y) (h : Hom Y Z) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- Forgetting local affineness retains the underlying locally topologically ringed space. -/
def forgetToLTRS : FormalScheme.{u} ⥤ LocallyTopologicallyRingedSpaceCat.{u} :=
  ObjectProperty.ι LocallyTopologicallyRingedSpaceCat.IsFormalScheme

/-- The underlying local morphism of the identity is the identity local morphism. -/
theorem id_toLTRSHom (X : FormalScheme.{u}) :
    (id X).toLTRSHom = LocallyTopologicallyRingedSpaceCat.id X.toLocallyTopologicallyRingedSpace :=
  rfl

/-- The underlying local morphism of a composite is the composite of the underlying morphisms. -/
theorem comp_toLTRSHom {X Y Z : FormalScheme.{u}} (f : Hom X Y) (g : Hom Y Z) :
    (comp f g).toLTRSHom = LocallyTopologicallyRingedSpaceCat.comp f.toLTRSHom g.toLTRSHom := rfl

end FormalScheme

end AlgebraicGeometry
