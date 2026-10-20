/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Comma.Arrow
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Presentable.ColimitPresentation
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.RingHom.IndEtale.Basic

@[expose] public section

/-!
# Filtered colimits of ind-etale ring maps

This module owns the categorical closure properties of
`RingHom.IndEtale.Raw`. It deliberately exposes only the
presentation and closure interfaces that downstream consumers need, rather
than a particular pair-stage construction of their proofs.

@stack 0BSJ
-/

open CategoryTheory Limits MorphismProperty
open CommRingCat CommRingCat.Hom

universe u v

namespace RingHom

namespace IndEtale.Raw

section

variable {R : Type u} [CommRing R]

/-- An ind-etale morphism in the under-category admits a filtered presentation
by etale under-objects. -/
@[stacks 0BSJ "ind-etale presentation"]
theorem under_presentation {S : Under (CommRingCat.of R)}
    (hS : ind.{v, u, u + 1} CommRingCat.etale S.hom) :
    ∃ (K : Type v) (_ : SmallCategory K) (_ : IsFiltered K)
      (pres : ColimitPresentation K S), ∀ k, CommRingCat.etale (pres.diag.obj k).hom := sorry

end

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {J : Type v} [Category.{v} J] [IsFiltered J]

/-- A filtered colimit of ind-etale `R`-algebras is ind-etale over `R`. -/
@[stacks 0BSJ "filtered colimits of ind-etale maps"]
theorem of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, ind.{v, u, u + 1} CommRingCat.etale (F.obj j).hom) :
    ind.{v, u, u + 1} CommRingCat.etale c.pt.hom := sorry

/-- Arbitrary-universe ring-map form of filtered-colimit closure, transported
through a chosen identification of the colimit object with an `R`-algebra. -/
theorem algebraMap_of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, ind.{v, u, u + 1} CommRingCat.etale (F.obj j).hom) :
    RingHom.IndEtale.Raw.{u, u, v} (algebraMap R A) := sorry

end

section

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- Arbitrary-universe form of directed-colimit closure for ind-etale
commutative-ring maps. -/
theorem colimit_of_directed
    (F : I ⥤ Arrow CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, RingHom.IndEtale.Raw.{u, u, v} (hom (F.obj i).hom)) :
    RingHom.IndEtale.Raw.{u, u, v} (hom c.pt.hom) := sorry

end

end IndEtale.Raw

namespace IndEtale

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable {J : Type v} [Category.{v} J] [IsFiltered J]

/-- A filtered colimit of ind-etale `R`-algebras is ind-etale, in ring-map
form. -/
@[stacks 0BSJ "filtered colimits of ind-etale maps"]
theorem of_isColimit
    (F : J ⥤ Under (CommRingCat.of R)) (c : Cocone F) (hc : IsColimit c)
    (e : c.pt ≅ Under.mk (CommRingCat.ofHom (algebraMap R A)))
    (hF : ∀ j, (hom (F.obj j).hom).IndEtale) :
    (algebraMap R A).IndEtale := sorry

end

section

variable {I : Type v} [Preorder I] [Nonempty I] [IsDirectedOrder I]

/-- The colimit map of a directed system of ind-etale commutative-ring maps is
ind-etale. -/
@[stacks 0GIM "directed colimits of ind-etale maps"]
theorem colimit_of_directed
    (F : I ⥤ Arrow CommRingCat.{u}) (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ i, (hom (F.obj i).hom).IndEtale) :
    (hom c.pt.hom).IndEtale := sorry

end

end IndEtale

end RingHom
