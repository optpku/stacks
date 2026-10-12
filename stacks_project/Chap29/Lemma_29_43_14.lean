/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Composition

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/-- Lemma 29.43.14: if `S` is quasi-compact and quasi-separated and `f : X ⟶ Y` and
`g : Y ⟶ S` are projective morphisms of schemes, then `f ≫ g` is projective. -/
@[stacks 0C4P]
theorem AlgebraicGeometry.Projective.comp_of_compactSpace_quasiSeparatedSpace
    {X Y S : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ S}
    [CompactSpace S] [QuasiSeparatedSpace S]
    (hf : Projective f) (hg : Projective g) :
    Projective (f ≫ g) := sorry
