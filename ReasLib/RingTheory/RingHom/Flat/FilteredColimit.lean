/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Under.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import ReasLib.Algebra.Category.CommRingCat.Under.Module
public import ReasLib.Algebra.Category.ModuleCat.FilteredColimit.Flat

/-!
# Flat maps and filtered colimits

This leaf transfers the filtered-colimit theorem for flat modules to
commutative algebras over a fixed base ring. The canonical presentation of
such algebras is `Under (CommRingCat.of R)`. It exposes both the ring-map
form, with an explicit mathematical hypothesis at every stage, and the
module form used when stage flatness is already available to typeclass search.

This is a support bridge, not a new source-tag owner: its proof uses
`CommRingCat.Under.forgetToModule` and
`ModuleCat.FilteredColimits.flat_of_isColimit`.
-/

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.Under
open CommRingCat CommRingCat.Hom

universe u v

namespace RingHom.Flat

/-- File-local canonical algebra structure on a commutative ring under the fixed base ring. -/
local instance underAlgebra {R : Type u} [CommRing R]
    (B : Under (CommRingCat.of R)) : Algebra R B.right :=
  B.hom.hom.toAlgebra

/-- The structural map of a selected filtered colimit cocone of flat
commutative `R`-algebras is flat. -/
theorem of_isColimit_under
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c)
    (hF : ∀ j, (hom (F.obj j).hom).Flat) :
    (hom c.pt.hom).Flat := sorry

/-- The underlying module of a selected filtered colimit cocone of flat
commutative `R`-algebras is flat. -/
theorem moduleFlat_of_isColimit_under
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R))
    (c : Cocone F) (hc : IsColimit c)
    [∀ j, Module.Flat R (F.obj j)] :
    Module.Flat R c.pt := sorry

/-- The structural map of the canonical filtered colimit of flat commutative
`R`-algebras is flat. -/
theorem of_colimit_under
    {R : Type u} [CommRing R]
    {J : Type v} [SmallCategory J] [IsFiltered J]
    (F : J ⥤ Under (CommRingCat.of R)) [HasColimit F]
    (hF : ∀ j, (hom (F.obj j).hom).Flat) :
    (hom (colimit F).hom).Flat := sorry

end RingHom.Flat
