/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Homology.DifferentialGradedModule.PropertyI.Resolution
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of property I resolutions

A map of resolutions records a strict map between the resolving DG modules together with its
compatibility with the maps from the original modules.  No existence theorem is asserted for
arbitrary fixed resolutions: downstream constructions consume a compatible map when one is
available, while change-of-resolution comparisons live canonically in the localized category.
-/

@[expose] public section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace DifferentialGradedModule.PropertyI.Resolution

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, v} R}

/-- A morphism of property I resolutions lying over a fixed morphism of right DG modules. -/
@[stacks 09KU "morphism of property-I resolutions"]
structure Map {M N : DifferentialGradedModule.{u, v} A} (f : M ⟶ N)
    (I : Resolution A M) (J : Resolution A N) where
  /-- The strict morphism between the resolving right DG modules. -/
  hom : I.obj ⟶ J.obj
  /-- Compatibility with the resolution morphisms. -/
  ι_naturality : I.ι ≫ hom = f ≫ J.ι

namespace Map

/-- Maps of property I resolutions are determined by their strict resolving morphisms. -/
@[ext, stacks 09KU "extensionality of maps of property-I resolutions"]
theorem ext {M N : DifferentialGradedModule.{u, v} A} {f : M ⟶ N}
    {I : Resolution A M} {J : Resolution A N} {m n : Map f I J}
    (h : m.hom = n.hom) : m = n := by
  cases m
  cases n
  cases h
  rfl

/-- The identity morphism satisfies the property I resolution comparison square. -/
@[stacks 09KU "identity map of a property-I resolution"]
theorem idNaturality {M : DifferentialGradedModule.{u, v} A} (I : Resolution A M) :
    I.ι ≫ 𝟙 I.obj = 𝟙 M ≫ I.ι := by
  simp

/-- The identity morphism of a property I resolution. -/
@[stacks 09KU "identity map of a property-I resolution"]
def id {M : DifferentialGradedModule.{u, v} A} (I : Resolution A M) :
    Map (𝟙 M) I I where
  hom := 𝟙 I.obj
  ι_naturality := idNaturality I

/-- The resolving morphism underlying the identity resolution map is the identity. -/
@[simp, stacks 09KU "identity map of a property-I resolution"]
theorem id_hom {M : DifferentialGradedModule.{u, v} A} (I : Resolution A M) :
    (id I).hom = 𝟙 I.obj := by
  rfl

/-- Composable resolution maps satisfy the comparison square for the composite base map. -/
@[stacks 09KU "composition of maps of property-I resolutions"]
theorem compNaturality {M N P : DifferentialGradedModule.{u, v} A}
    {f : M ⟶ N} {g : N ⟶ P}
    {I : Resolution A M} {J : Resolution A N} {K : Resolution A P}
    (m : Map f I J) (n : Map g J K) :
    I.ι ≫ (m.hom ≫ n.hom) = (f ≫ g) ≫ K.ι := by
  calc
    I.ι ≫ (m.hom ≫ n.hom) = (I.ι ≫ m.hom) ≫ n.hom := (Category.assoc _ _ _).symm
    _ = (f ≫ J.ι) ≫ n.hom := by rw [m.ι_naturality]
    _ = f ≫ (J.ι ≫ n.hom) := Category.assoc _ _ _
    _ = f ≫ (g ≫ K.ι) := by rw [n.ι_naturality]
    _ = (f ≫ g) ≫ K.ι := (Category.assoc _ _ _).symm

/-- Composition of maps of property I resolutions. -/
@[stacks 09KU "composition of maps of property-I resolutions"]
def comp {M N P : DifferentialGradedModule.{u, v} A}
    {f : M ⟶ N} {g : N ⟶ P}
    {I : Resolution A M} {J : Resolution A N} {K : Resolution A P}
    (m : Map f I J) (n : Map g J K) : Map (f ≫ g) I K where
  hom := m.hom ≫ n.hom
  ι_naturality := compNaturality m n

/-- The resolving morphism underlying a composite is the composite resolving morphism. -/
@[simp, stacks 09KU "composition of maps of property-I resolutions"]
theorem comp_hom {M N P : DifferentialGradedModule.{u, v} A}
    {f : M ⟶ N} {g : N ⟶ P}
    {I : Resolution A M} {J : Resolution A N} {K : Resolution A P}
    (m : Map f I J) (n : Map g J K) :
    (comp m n).hom = m.hom ≫ n.hom := by
  rfl

/-- Reindexing a resolution map along an equality of base morphisms preserves its comparison
square. -/
@[stacks 09KU "reindexing a map of property-I resolutions"]
theorem reindexNaturality {M N : DifferentialGradedModule.{u, v} A}
    {f g : M ⟶ N} {I : Resolution A M} {J : Resolution A N}
    (h : f = g) (m : Map f I J) : I.ι ≫ m.hom = g ≫ J.ι := by
  simpa [h] using m.ι_naturality

/-- Reindex a map of property I resolutions along an equality of base morphisms. -/
@[stacks 09KU "reindexing a map of property-I resolutions"]
def reindex {M N : DifferentialGradedModule.{u, v} A}
    {f g : M ⟶ N} {I : Resolution A M} {J : Resolution A N}
    (h : f = g) (m : Map f I J) : Map g I J where
  hom := m.hom
  ι_naturality := reindexNaturality h m

/-- Reindexing does not change the strict resolving morphism. -/
@[simp, stacks 09KU "reindexing a map of property-I resolutions"]
theorem reindex_hom {M N : DifferentialGradedModule.{u, v} A}
    {f g : M ⟶ N} {I : Resolution A M} {J : Resolution A N}
    (h : f = g) (m : Map f I J) : (reindex h m).hom = m.hom := by
  rfl

/-- Reindexing along reflexivity leaves a resolution map unchanged. -/
@[simp, stacks 09KU "reindexing a map of property-I resolutions"]
theorem reindex_rfl {M N : DifferentialGradedModule.{u, v} A}
    {f : M ⟶ N} {I : Resolution A M} {J : Resolution A N}
    (m : Map f I J) : reindex rfl m = m := by
  rfl

/-- Identity is a left unit for maps of property I resolutions, up to reindexing. -/
@[stacks 09KU "left identity for maps of property-I resolutions"]
theorem id_comp {M N : DifferentialGradedModule.{u, v} A}
    {f : M ⟶ N} {I : Resolution A M} {J : Resolution A N}
    (m : Map f I J) :
    reindex (Category.id_comp f) (comp (id I) m) = m := by
  apply ext
  simp

/-- Identity is a right unit for maps of property I resolutions, up to reindexing. -/
@[stacks 09KU "right identity for maps of property-I resolutions"]
theorem comp_id {M N : DifferentialGradedModule.{u, v} A}
    {f : M ⟶ N} {I : Resolution A M} {J : Resolution A N}
    (m : Map f I J) :
    reindex (Category.comp_id f) (comp m (id J)) = m := by
  apply ext
  simp

/-- Composition of maps of property I resolutions is associative, up to reindexing. -/
@[stacks 09KU "associativity of maps of property-I resolutions"]
theorem assoc {M N P Q : DifferentialGradedModule.{u, v} A}
    {f : M ⟶ N} {g : N ⟶ P} {h : P ⟶ Q}
    {I : Resolution A M} {J : Resolution A N}
    {K : Resolution A P} {L : Resolution A Q}
    (m : Map f I J) (n : Map g J K) (k : Map h K L) :
    reindex (Category.assoc f g h) (comp (comp m n) k) = comp m (comp n k) := by
  apply ext
  simp [Category.assoc]

end Map

end DifferentialGradedModule.PropertyI.Resolution
