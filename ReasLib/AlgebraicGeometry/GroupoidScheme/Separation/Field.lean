/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Separation
public import ReasLib.AlgebraicGeometry.GroupScheme.Separation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Affine.Artinian

/-!
# Separatedness of groupoid schemes over fields

This module establishes separatedness of the arrow scheme of a groupoid scheme whose object
scheme is the spectrum of a field.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/-- The arrow scheme of a groupoid scheme is separated when its object scheme is isomorphic to
the spectrum of a field. -/
theorem isSeparatedArrowOfField {S : Scheme.{u}} (G : GroupoidScheme S)
    {k : Type u} [Field k] (eU : Spec (CommRingCat.of k) ≅ G.U.left) :
    Scheme.IsSeparated G.R.left := sorry

end AlgebraicGeometry.GroupoidScheme
