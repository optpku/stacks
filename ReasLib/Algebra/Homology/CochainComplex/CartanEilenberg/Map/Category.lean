/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Map.Definition
public import ReasLib.Algebra.Homology.CochainComplex.CartanEilenberg.Existence

/-!
# The category of Cartan--Eilenberg resolutions

This leaf bundles a bounded-below source complex with a chosen Cartan--Eilenberg resolution.
The source complex and resolving double complex are then honest functors, so constructions on
resolution maps can be assembled functorially without repeating identity and composition laws.
-/

@[expose] public section

open CategoryTheory ComplexShape HomologicalComplex₂

noncomputable section

universe v u

namespace CochainComplex.CartanEilenbergResolution

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- A bounded-below cochain complex equipped with a chosen Cartan--Eilenberg resolution. -/
@[stacks 015J "category of Cartan-Eilenberg resolutions"]
structure Bundled (A : Type u) [Category.{v} A] [Abelian A] where
  /-- The bounded-below source complex. -/
  base : CochainComplex.Plus A
  /-- The chosen Cartan--Eilenberg resolution of the source. -/
  resolution : CartanEilenbergResolution base

namespace Bundled

/-- Cartan--Eilenberg resolution maps give the morphisms of bundled resolutions. -/
@[stacks 015J "category of Cartan-Eilenberg resolutions"]
instance category : Category.{v} (Bundled A) where
  Hom X Y := Map X.resolution Y.resolution
  id X := Map.id X.resolution
  comp f g := Map.comp f g
  id_comp := Map.id_comp
  comp_id := Map.comp_id
  assoc := Map.comp_assoc

/-- Forget a bundled Cartan--Eilenberg resolution to its bounded-below source complex. -/
@[stacks 015J "source functor of Cartan-Eilenberg resolutions"]
def source (A : Type u) [Category.{v} A] [Abelian A] :
    Bundled A ⥤ CochainComplex.Plus A where
  obj X := X.base
  map f := f.base
  map_id X := Map.id_base X.resolution
  map_comp f g := Map.comp_base f g

/-- Retain the resolving double complex of a bundled Cartan--Eilenberg resolution. -/
@[stacks 015J "double-complex functor of Cartan-Eilenberg resolutions"]
def bicomplex (A : Type u) [Category.{v} A] [Abelian A] :
    Bundled A ⥤ HomologicalComplex₂ A (up ℤ) (up ℤ) where
  obj X := X.resolution.bicomplex
  map f := f.hom
  map_id X := Map.id_hom X.resolution
  map_comp f g := Map.comp_hom f g

/-- The source functor returns the stored bounded-below complex. -/
@[simp, stacks 015J "source functor of Cartan-Eilenberg resolutions"]
theorem source_obj (X : Bundled A) : (source A).obj X = X.base := sorry

/-- The source functor returns the bundled base map of a resolution morphism. -/
@[simp, stacks 015J "source functor of Cartan-Eilenberg resolutions"]
theorem source_map {X Y : Bundled A} (f : X ⟶ Y) :
    (source A).map f = f.base := sorry

/-- The double-complex functor returns the stored resolving double complex. -/
@[simp, stacks 015J "double-complex functor of Cartan-Eilenberg resolutions"]
theorem bicomplex_obj (X : Bundled A) :
    (bicomplex A).obj X = X.resolution.bicomplex := sorry

/-- The double-complex functor returns the stored map of resolving double complexes. -/
@[simp, stacks 015J "double-complex functor of Cartan-Eilenberg resolutions"]
theorem bicomplex_map {X Y : Bundled A} (f : X ⟶ Y) :
    (bicomplex A).map f = f.hom := sorry

/-- Every morphism of source complexes lifts to a morphism of bundled
Cartan--Eilenberg resolutions. -/
@[stacks 015J "full source functor of Cartan-Eilenberg resolutions"]
noncomputable instance source_full : (source A).Full := sorry

/-- If the source category has enough injectives, every bounded-below complex is represented
by a bundled Cartan--Eilenberg resolution. -/
@[stacks 015I "essentially surjective source functor of Cartan-Eilenberg resolutions"]
noncomputable instance source_essSurj [EnoughInjectives A] : (source A).EssSurj := sorry

#synth (source A).Full

end Bundled

end CochainComplex.CartanEilenbergResolution
