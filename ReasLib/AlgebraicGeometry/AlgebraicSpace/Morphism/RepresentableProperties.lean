/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Representable properties of transformations of presheaves over a base scheme

For a property `P` of morphisms of schemes, a transformation `a : F ⟶ G` of presheaves on
`Sch/S` has representable property `P` if it is representable and every scheme base change
`V_ξ ⟶ U` has `P`. The canonical
expression is mathlib's `(MorphismProperty.over P).presheaf`; this file only fixes reducible
names for the three instances used by the étale site and open-subspace API.

These names are presheaf-level on purpose: they apply to transformations whose source is
not yet known to be an algebraic space (for example atlases of a presheaf fiber product
before it is shown to be an algebraic space, or the arrows of the small étale chart
category as a `MorphismProperty`). On morphisms of algebraic spaces,
`Representable.IsOpenImmersion` is exactly the field of the canonical class
`AlgebraicSpace.IsOpenImmersion` (`Immersion.lean`), whose bridge
`AlgebraicSpace.isOpenImmersion_iff` has right-hand side reducibly equal to
`Representable.IsOpenImmersion f`; the quasi-compact bridge is `AlgebraicSpace.quasiCompact_presheaf_iff_quasiCompact` and the
étale bridge for charts is `AlgebraicSpace.SmallEtale.etale_iff`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Representable

/-- A transformation of presheaves on schemes over a base is representably étale if it is
representable and all its scheme base changes are étale. -/
abbrev Etale {S : Scheme.{u}} : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.over (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u})).presheaf

/-- A transformation of presheaves on schemes over a base is a representable open immersion
if it is representable and all its scheme base changes are open immersions. -/
abbrev IsOpenImmersion {S : Scheme.{u}} : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.over
    (@AlgebraicGeometry.IsOpenImmersion : MorphismProperty Scheme.{u})).presheaf

/-- A transformation of presheaves on schemes over a base is representably quasi-compact
if it is representable and all its scheme base changes are quasi-compact. -/
abbrev QuasiCompact {S : Scheme.{u}} : MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  (MorphismProperty.over (@AlgebraicGeometry.QuasiCompact : MorphismProperty Scheme.{u})).presheaf

/-- Every representable open immersion of presheaves is representably étale. -/
theorem isOpenImmersion_etale {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u}
    (ι : F ⟶ G) (h_open : IsOpenImmersion ι) : Etale ι := sorry

end AlgebraicGeometry.AlgebraicSpace.Representable
