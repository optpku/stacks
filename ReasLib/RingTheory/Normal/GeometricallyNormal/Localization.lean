/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Normal.GeometricallyNormal
public import ReasLib.RingTheory.Normal.Localization

/-!
# Geometric normality under localization

Geometric normality of field algebras is inherited by arbitrary localizations
and by canonical localization algebras.
-/

@[expose] public section

universe u v w

namespace Algebra.IsGeometricallyNormal

/-- An arbitrary localization of a geometrically normal field algebra is
geometrically normal. -/
@[stacks 06DE]
theorem of_isLocalization
    {k : Type u} {A : Type v} {B : Type w}
    [Field k] [CommRing A] [CommRing B]
    [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]
    (S : Submonoid A) [IsLocalization S B] [IsGeometricallyNormal k A] :
    IsGeometricallyNormal k B := sorry

end Algebra.IsGeometricallyNormal

namespace Localization

/-- The canonical localization of a geometrically normal field algebra is
geometrically normal. -/
@[stacks 06DE "geometrically normal localization instance"]
instance instIsGeometricallyNormal
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    (S : Submonoid A) [Algebra.IsGeometricallyNormal k A] :
    Algebra.IsGeometricallyNormal k (Localization S) := sorry

end Localization
