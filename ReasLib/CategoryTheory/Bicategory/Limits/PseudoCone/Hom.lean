/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.Bilimit.Basic

/-!
# Morphisms of conical pseudocones

This neutral leaf exposes the apex-map and comparison-modification description of morphisms
between varying-apex pseudocones, together with the corresponding `2`-morphism API. It is a
domain-specific facade over `ColaxCostructuredArrow`; no bilimit hypothesis is needed.

The cone and its represented `IsBilimit` property remain owned by `Bilimit.Basic`. Keeping this
morphism layer here lets transport, pseudopullback, and other universal-property consumers reuse
ordinary pseudocone maps without importing bilimit lifts or equivalence constructions.
-/

@[expose] public section

open scoped CategoryTheory.Bicategory

universe w v u wJ vJ uJ

namespace CategoryTheory

open Bicategory
open scoped Pseudofunctor.StrongTrans

namespace Bicategory.PseudoCone

variable {B : Type u} [Bicategory.{w, v} B]
variable {J : Type uJ} [Bicategory.{wJ, vJ} J]
variable {F : J ⥤ᵖ B}

/-- The map between apexes carried by a morphism of varying-apex pseudocones. -/
abbrev map {S T : PseudoCone F} (u : S ⟶ T) : S.pt ⟶ T.pt :=
  ColaxCostructuredArrow.map u

/-- The comparison modification carried by a morphism of varying-apex pseudocones.

Writing `const(X)` for `Pseudofunctor.const J X`, this modification has boundary
`const(map u) ≫ T.π ⟶ S.π`. It is the domain-specific projection of the generic
`ColaxCostructuredArrow.fac` API. -/
abbrev fac {S T : PseudoCone F} (u : S ⟶ T) :
    (T.comparison S.pt).obj (PseudoCone.map u) ⟶ S.π :=
  ColaxCostructuredArrow.fac u

/-- Construct a morphism of varying-apex pseudocones from its apex map and an arbitrary
comparison modification. No invertibility hypothesis is imposed on the modification. -/
def homMk {S T : PseudoCone F} (l : S.pt ⟶ T.pt)
    (e : (T.comparison S.pt).obj l ⟶ S.π) : S ⟶ T :=
  ColaxCostructuredArrow.homMk l e

/-- The apex map of a constructed pseudocone morphism is the supplied map. -/
@[simp]
theorem homMk_map {S T : PseudoCone F} (l : S.pt ⟶ T.pt)
    (e : (T.comparison S.pt).obj l ⟶ S.π) :
    map (homMk l e) = l := sorry

/-- The comparison modification of a constructed pseudocone morphism is the supplied
modification. -/
@[simp]
theorem homMk_fac {S T : PseudoCone F} (l : S.pt ⟶ T.pt)
    (e : (T.comparison S.pt).obj l ⟶ S.π) :
    fac (homMk l e) = e := sorry

/-- Pseudocone morphisms are determined by their apex maps and normalized comparison
modifications. -/
@[ext (iff := false)]
theorem hom_ext {S T : PseudoCone F} (u v : S ⟶ T)
    (hmap : map u = map v)
    (hfac : (T.comparison S.pt).map (eqToHom hmap) ≫ fac v = fac u) :
    u = v := sorry

/-- Reconstructing a pseudocone morphism from its apex map and comparison modification
recovers the original morphism. -/
@[simp]
theorem homMk_map_fac {S T : PseudoCone F} (u : S ⟶ T) :
    homMk (map u) (fac u) = u := sorry

/-- The component at `j` of the comparison carried by a pseudocone morphism. -/
abbrev facApp {S T : PseudoCone F} (u : S ⟶ T) (j : J) :
    PseudoCone.map u ≫ T.π.app j ⟶ S.π.app j :=
  (PseudoCone.fac u).as.app j

/-- In a locally groupoidal ambient bicategory, the component comparison of a pseudocone
morphism as an isomorphism.

The local-groupoid hypothesis is needed only for this isomorphism view, not for the underlying
cone morphism. -/
noncomputable abbrev facAppIso [IsLocallyGroupoid B]
    {S T : PseudoCone F} (u : S ⟶ T) (j : J) :
    PseudoCone.map u ≫ T.π.app j ≅ S.π.app j :=
  asIso (PseudoCone.facApp u j)

/-- The ambient `2`-morphism between apex maps underlying a `2`-morphism of pseudocones. -/
abbrev map₂ {S T : PseudoCone F} {u v : S ⟶ T} (η : u ⟶ v) :
    PseudoCone.map u ⟶ PseudoCone.map v :=
  ColaxCostructuredArrow.map₂ η

/-- Every pseudocone `2`-morphism is compatible with the normalized comparison
modifications of its source and target. -/
theorem map₂_fac {S T : PseudoCone F} {u v : S ⟶ T} (η : u ⟶ v) :
    (T.comparison S.pt).map (map₂ η) ≫ fac v = fac u := sorry

/-- Construct a pseudocone `2`-morphism from a cell between apex maps satisfying the
normalized comparison equation. -/
def hom₂Mk {S T : PseudoCone F} {u v : S ⟶ T}
    (η : map u ⟶ map v)
    (comm : (T.comparison S.pt).map η ≫ fac v = fac u) : u ⟶ v :=
  ColaxCostructuredArrow.hom₂Mk η comm

/-- The apex cell of a constructed pseudocone `2`-morphism is the supplied cell. -/
@[simp]
theorem hom₂Mk_map₂ {S T : PseudoCone F} {u v : S ⟶ T}
    (η : map u ⟶ map v)
    (comm : (T.comparison S.pt).map η ≫ fac v = fac u) :
    map₂ (hom₂Mk η comm) = η := sorry

/-- Pseudocone `2`-morphisms are determined by their cells between apex maps. -/
@[ext]
theorem hom₂_ext {S T : PseudoCone F} {u v : S ⟶ T} {η θ : u ⟶ v}
    (h : map₂ η = map₂ θ) : η = θ := sorry

/-- Reconstructing a pseudocone `2`-morphism from its apex cell and compatibility equation
recovers the original `2`-morphism. -/
@[simp]
theorem hom₂Mk_map₂_fac {S T : PseudoCone F} {u v : S ⟶ T} (η : u ⟶ v) :
    hom₂Mk (map₂ η) (map₂_fac η) = η := sorry

/- Data and axiom audit (mathlib 4.32):

`homMk` and `hom₂Mk` delegate their non-`Prop` fields to the explicit constructors of
`ColaxCostructuredArrow`. Any `sorryAx` dependency is confined to equality, compatibility,
and inherited coherence proofs; it does not choose an apex map, comparison modification,
or apex `2`-cell. -/

end Bicategory.PseudoCone

end CategoryTheory
