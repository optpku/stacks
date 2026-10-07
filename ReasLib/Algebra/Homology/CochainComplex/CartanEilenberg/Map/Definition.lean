module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maps of Cartan--Eilenberg resolutions

This file owns the data of a map of Cartan--Eilenberg resolutions, together with its identity,
composition, and source-complex API.  Views of such a map on columns, rows, and homology objects
are kept in `CartanEilenberg.Map.Views`.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]
variable {K L M : CochainComplex.Plus A}

/-- A map between Cartan--Eilenberg resolutions.

The map of source cochain complexes and the map of resolving double complexes are required to
commute with the augmentations.  No derived functor or spectral sequence is part of this data. -/
@[stacks 015J "map of Cartan-Eilenberg resolutions"]
structure Map (I : CartanEilenbergResolution K) (J : CartanEilenbergResolution L) where
  /-- The map between the source cochain complexes. -/
  base : K ⟶ L
  /-- The map between the resolving double complexes. -/
  hom : I.bicomplex ⟶ J.bicomplex
  /-- The source and double-complex maps commute with the bottom-row augmentations. -/
  augmentation_naturality :
    I.augmentation ≫ ((flipFunctor A (up ℤ) (up ℤ)).map hom).f 0 =
      base.hom ≫ J.augmentation

attribute [reassoc] Map.augmentation_naturality

namespace Map

variable {I : CartanEilenbergResolution K} {J : CartanEilenbergResolution L}
variable {N : CartanEilenbergResolution M}

/-- The identity source and double-complex maps commute with the augmentation. -/
theorem id_augmentation_naturality (I : CartanEilenbergResolution K) :
    I.augmentation ≫ ((flipFunctor A (up ℤ) (up ℤ)).map (𝟙 I.bicomplex)).f 0 =
      (𝟙 K.obj) ≫ I.augmentation := sorry

/-- The identity map of a Cartan--Eilenberg resolution. -/
@[stacks 015J "identity map of a Cartan-Eilenberg resolution"]
def id (I : CartanEilenbergResolution K) : Map I I where
  base := 𝟙 K
  hom := 𝟙 I.bicomplex
  augmentation_naturality := id_augmentation_naturality I

/-- Composites of augmentation-compatible resolution maps remain augmentation-compatible. -/
theorem comp_augmentation_naturality (f : Map I J) (g : Map J N) :
    I.augmentation ≫
        ((flipFunctor A (up ℤ) (up ℤ)).map (f.hom ≫ g.hom)).f 0 =
      (f.base ≫ g.base).hom ≫ N.augmentation := sorry

/-- Composition of maps of Cartan--Eilenberg resolutions. -/
@[stacks 015J "composition of Cartan-Eilenberg resolution maps"]
def comp (f : Map I J) (g : Map J N) : Map I N where
  base := f.base ≫ g.base
  hom := f.hom ≫ g.hom
  augmentation_naturality := comp_augmentation_naturality f g

/-- Maps of Cartan--Eilenberg resolutions are determined by their base and double-complex maps. -/
@[ext]
theorem ext (f g : Map I J) (hbase : f.base = g.base) (hhom : f.hom = g.hom) :
    f = g := sorry

/-- The base map of an identity resolution map is the identity. -/
@[simp]
theorem id_base (I : CartanEilenbergResolution K) : (id I).base = 𝟙 K := sorry

/-- The double-complex map of an identity resolution map is the identity. -/
@[simp]
theorem id_hom (I : CartanEilenbergResolution K) : (id I).hom = 𝟙 I.bicomplex := sorry

/-- The base map of a composite is the composite of the base maps. -/
@[simp, reassoc]
theorem comp_base (f : Map I J) (g : Map J N) :
    (comp f g).base = f.base ≫ g.base := sorry

/-- The double-complex map of a composite is the composite double-complex map. -/
@[simp, reassoc]
theorem comp_hom (f : Map I J) (g : Map J N) :
    (comp f g).hom = f.hom ≫ g.hom := sorry

/-- Identity is a left unit for maps of Cartan--Eilenberg resolutions. -/
@[simp]
theorem id_comp (f : Map I J) : comp (id I) f = f := sorry

/-- Identity is a right unit for maps of Cartan--Eilenberg resolutions. -/
@[simp]
theorem comp_id (f : Map I J) : comp f (id J) = f := sorry

/-- Composition of maps of Cartan--Eilenberg resolutions is associative. -/
theorem comp_assoc {P : CochainComplex.Plus A}
    {O : CartanEilenbergResolution P}
    (f : Map I J) (g : Map J N) (h : Map N O) :
    comp (comp f g) h = comp f (comp g h) := sorry

/-- Every map of bounded-below source complexes admits a map between specified
Cartan--Eilenberg resolutions lifting it.  The lift is not asserted to be canonical. -/
@[stacks 015J "existence of a Cartan-Eilenberg resolution map"]
theorem exists_lift (I : CartanEilenbergResolution K)
    (J : CartanEilenbergResolution L) (f : K ⟶ L) :
    ∃ g : Map I J, g.base = f := sorry

end Map

end CochainComplex.CartanEilenbergResolution
