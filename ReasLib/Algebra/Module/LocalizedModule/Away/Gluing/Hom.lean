/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Morphisms of Principal-Open Module Gluing Data

This leaf packages compatible maps between local pieces.  The pairwise overlap
square implies that the coordinatewise map preserves compatible families, and
therefore induces a map of glued modules.
-/

@[expose] public section

open CategoryTheory
open scoped ModuleCat.Algebra

universe u v w

namespace LocalizedModule.Away.Gluing

variable {R : Type u} [CommRing R]
variable {ι : Type w}
variable {f : ι → R}

/-- Tag `00EK`: a morphism of principal-open module gluing data.  Its local
maps commute with all overlap identifications. -/
@[stacks 00EK "principal-open module gluing morphism"]
structure Hom (X Y : Gluing f) where
  /-- The map on the local module over each principal open. -/
  hom : ∀ i : ι, X.localModule i ⟶ Y.localModule i
  /-- Naturality of the local maps on each pairwise overlap, as a square of
  modules over the overlap localization ring. -/
  comm : ∀ i j : ι,
    CommSq
      (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
        ((hom i).hom.restrictScalars R))
      (X.overlapIso i j).hom
      (Y.overlapIso i j).hom
      (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
        ((hom j).hom.restrictScalars R))

namespace Hom

variable {X Y : Gluing f} (φ : Hom X Y)

/-- The underlying base-ring-linear map on the family of local sections. -/
@[stacks 00EK "principal-open gluing morphism family map"]
def familyMap :
    (∀ i : ι, X.localModule i) →ₗ[R] ∀ i : ι, Y.localModule i :=
  LinearMap.piMap fun i ↦ (φ.hom i).hom.restrictScalars R

/-- The family map of a gluing morphism is coordinatewise its local map. -/
@[simp, stacks 00EK "principal-open gluing morphism family map application"]
theorem familyMap_apply (x : ∀ i : ι, X.localModule i) (i : ι) :
    φ.familyMap x i = φ.hom i (x i) := sorry

/-- The coordinatewise map on the pairwise-overlap families induced by a
gluing morphism. -/
@[stacks 00EK "principal-open gluing morphism overlap family map"]
noncomputable def overlapMap :
    (∀ i : ι, ∀ j : ι,
        LocalizedModule.Away (f i * f j) (X.localModule i)) →ₗ[R]
      ∀ i : ι, ∀ j : ι,
        LocalizedModule.Away (f i * f j) (Y.localModule i) :=
  LinearMap.piMap fun i ↦ LinearMap.piMap fun j ↦
    LocalizedModule.Away.map (f i * f j) ((φ.hom i).hom.restrictScalars R)

/-- The overlap-family map acts in its `(i, j)` coordinate by localizing the
`i`-th local morphism. -/
@[simp, stacks 00EK "principal-open gluing morphism overlap family map application"]
theorem overlapMap_apply
    (x : ∀ i : ι, ∀ j : ι,
      LocalizedModule.Away (f i * f j) (X.localModule i)) (i j : ι) :
    φ.overlapMap x i j =
      LocalizedModule.Away.map (f i * f j) ((φ.hom i).hom.restrictScalars R)
        (x i j) := sorry

/-- The local overlap square sends every compatible family to a compatible
family. -/
@[stacks 00EK "principal-open gluing morphism preserves compatible families"]
theorem familyMap_mem_gluedModule (x : ∀ i : ι, X.localModule i)
    (hx : x ∈ X.gluedModule) :
    φ.familyMap x ∈ Y.gluedModule := sorry

/-- The map induced by a gluing morphism on the modules of compatible local
sections. -/
@[stacks 00EK "principal-open gluing morphism on glued modules"]
noncomputable def gluedMap : X.gluedModule →ₗ[R] Y.gluedModule :=
  (φ.familyMap.comp X.gluedModule.subtype).codRestrict Y.gluedModule
    fun x ↦ φ.familyMap_mem_gluedModule x.1 x.2

/-- Two gluing morphisms are equal when their local maps are equal.  The
overlap squares are propositions and the glued map is derived from the local
maps. -/
@[ext, stacks 00EK "principal-open gluing morphism extensionality"]
theorem ext {φ ψ : Hom X Y}
    (hlocal : ∀ i : ι, φ.hom i = ψ.hom i) :
    φ = ψ := sorry

/-- The induced glued-module map has the expected `i`-th local coordinate. -/
@[stacks 00EK "principal-open gluing morphism projection"]
theorem projection_gluedMap (i : ι) :
    (Y.projection i).comp φ.gluedMap =
      ((φ.hom i).hom.restrictScalars R).comp (X.projection i) := sorry

/-- The induced glued-module map is coordinatewise the supplied local map. -/
@[simp, stacks 00EK "principal-open gluing morphism coordinate application"]
theorem gluedMap_apply (x : X.gluedModule) (i : ι) :
    (φ.gluedMap x).1 i = φ.hom i (x.1 i) := sorry

/-- The local overlap square of a gluing morphism, evaluated as an equality
of base-ring-linear maps. -/
@[stacks 00EK "principal-open gluing morphism overlap square after scalar restriction"]
theorem comm_restrictScalars (i j : ι) :
    (LocalizedModule.Away.map (f i * f j)
        ((φ.hom j).hom.restrictScalars R)).comp
        ((X.overlapIso i j).toLinearEquiv.restrictScalars R).toLinearMap =
      ((Y.overlapIso i j).toLinearEquiv.restrictScalars R).toLinearMap.comp
        (LocalizedModule.Away.map (f i * f j)
          ((φ.hom i).hom.restrictScalars R)) := sorry

/-- The coordinatewise maps of a gluing morphism commute with the two-term
principal-open compatibility maps. -/
@[stacks 00EK "principal-open gluing morphism compatibility naturality"]
theorem compatibilityMap_naturality :
    Y.compatibilityMap.comp φ.familyMap = φ.overlapMap.comp X.compatibilityMap := sorry

/-- The inclusion of the glued target family after the induced map is the
underlying coordinatewise family map. -/
@[simp, stacks 00EK "principal-open gluing morphism subtype composition"]
theorem subtype_comp_gluedMap :
    Y.gluedModule.subtype.comp φ.gluedMap =
      φ.familyMap.comp X.gluedModule.subtype := sorry

/-- Localizing the induced glued-module map commutes with the local
projection to every member of the principal-open family. -/
@[stacks 00EK "principal-open gluing morphism localized projection naturality"]
theorem localizedProjection_naturality (i : ι) :
    (Y.localizedProjection i).comp
        (LocalizedModule.map (Submonoid.powers (f i)) φ.gluedMap) =
      (φ.hom i).hom.comp (X.localizedProjection i) := sorry

/-- Identity local morphisms commute with every principal-open overlap
identification. -/
@[stacks 00EK "principal-open gluing identity overlap square"]
theorem id_comm (X : Gluing f) :
    ∀ i j : ι,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
          (LinearMap.id : X.localModule i →ₗ[R] X.localModule i))
        (X.overlapIso i j).hom
        (X.overlapIso i j).hom
        (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
          (LinearMap.id : X.localModule j →ₗ[R] X.localModule j)) := sorry

/-- The identity morphism of principal-open module gluing data. -/
@[stacks 00EK "principal-open gluing identity morphism"]
def id (X : Gluing f) : Hom X X where
  hom i := 𝟙 (X.localModule i)
  comm := id_comm X

/-- The local component of the identity gluing morphism is the identity. -/
@[simp, stacks 00EK "principal-open gluing identity component"]
theorem id_hom (X : Gluing f) (i : ι) :
    (id X).hom i = 𝟙 (X.localModule i) := sorry

/-- Componentwise composites of compatible gluing morphisms commute with all
principal-open overlap identifications. -/
@[stacks 00EK "principal-open gluing composition overlap square"]
theorem comp_comm {X Y Z : Gluing f} (φ : Hom X Y) (ψ : Hom Y Z) :
    ∀ i j : ι,
      CommSq
        (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
          ((φ.hom i ≫ ψ.hom i).hom.restrictScalars R))
        (X.overlapIso i j).hom
      (Z.overlapIso i j).hom
      (ModuleCat.ofHom <| LocalizedModule.map (Submonoid.powers (f i * f j))
        ((φ.hom j ≫ ψ.hom j).hom.restrictScalars R)) := sorry

/-- Composition of principal-open module gluing morphisms. -/
@[stacks 00EK "principal-open gluing morphism composition"]
def comp {X Y Z : Gluing f} (φ : Hom X Y) (ψ : Hom Y Z) : Hom X Z where
  hom i := φ.hom i ≫ ψ.hom i
  comm := comp_comm φ ψ

/-- The local component of a composite gluing morphism is the composite of
its local components. -/
@[simp, stacks 00EK "principal-open gluing morphism composition component"]
theorem comp_hom {X Y Z : Gluing f} (φ : Hom X Y) (ψ : Hom Y Z) (i : ι) :
    (comp φ ψ).hom i = φ.hom i ≫ ψ.hom i := sorry

/-- Left identity for principal-open module gluing morphisms. -/
@[stacks 00EK "principal-open gluing morphism left identity"]
theorem id_comp {X Y : Gluing f} (φ : Hom X Y) :
    comp (id X) φ = φ := sorry

/-- Right identity for principal-open module gluing morphisms. -/
@[stacks 00EK "principal-open gluing morphism right identity"]
theorem comp_id {X Y : Gluing f} (φ : Hom X Y) :
    comp φ (id Y) = φ := sorry

/-- Associativity of componentwise composition of principal-open module
gluing morphisms. -/
@[stacks 00EK "principal-open gluing morphism associativity"]
theorem assoc {W X Y Z : Gluing f}
    (φ : Hom W X) (ψ : Hom X Y) (χ : Hom Y Z) :
    comp (comp φ ψ) χ = comp φ (comp ψ χ) := sorry

/-- The glued-module map induced by the identity gluing morphism is the
identity linear map. -/
@[simp, stacks 00EK "principal-open gluing identity induced map"]
theorem gluedMap_id (X : Gluing f) :
    (id X).gluedMap = LinearMap.id := sorry

/-- The glued-module map induced by a composite is the composite of the
induced glued-module maps. -/
@[simp, stacks 00EK "principal-open gluing composition induced map"]
theorem gluedMap_comp {X Y Z : Gluing f} (φ : Hom X Y) (ψ : Hom Y Z) :
    (comp φ ψ).gluedMap = ψ.gluedMap.comp φ.gluedMap := sorry

end Hom

/-- Tag `00EK`: principal-open module gluing data form a category under
compatible local morphisms. -/
@[stacks 00EK "principal-open module gluing category"]
instance instCategory : Category (Gluing f) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

end LocalizedModule.Away.Gluing
