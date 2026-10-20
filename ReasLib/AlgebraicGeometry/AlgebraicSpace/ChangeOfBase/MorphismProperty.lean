/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Equivalence

/-!
# Morphism properties under change of base for algebraic spaces

Viewing a scheme-to-algebraic-space morphism over another base preserves and reflects
scheme-morphism properties stable under base change and fppf local at the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Viewing a morphism from a scheme to an algebraic space over another base preserves
and reflects every scheme-morphism property stable under base change and fppf local
at the target. -/
theorem extendBaseMap_over_presheaf_iff {S S' : Scheme.{u}} (g : S ⟶ S')
    {F : AlgebraicSpace S} {T : Over S} (f : ofOver T ⟶ F)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage] :
    (over P).presheaf (extendBaseMap g f) ↔ (over P).presheaf f :=
  sorry

/-- After identifying the extended representable domain with the same scheme over
the new base via the canonical Yoneda isomorphism, extension preserves and reflects
every scheme-morphism property stable under base change and fppf local at the target. -/
theorem extendBaseMap_ofOver_over_presheaf_iff {S S' : Scheme.{u}} (g : S ⟶ S')
    {F : AlgebraicSpace S} {T : Over S} (f : ofOver T ⟶ F)
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    [P.IsLocalAtTarget Scheme.fppfPrecoverage] :
    (over P).presheaf ((extendBasePresheafYonedaIso g T).inv ≫ extendBaseMap g f) ↔
      (over P).presheaf f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
