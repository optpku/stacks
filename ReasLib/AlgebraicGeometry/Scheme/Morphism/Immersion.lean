/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Tactic.CrossRefAttribute

/-!
# Immersion properties of equalizers of scheme morphisms
-/

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- Lemma 26.21.5: the equalizer inclusion in a scheme slice is an immersion. -/
@[stacks 01KM "equalizer immersion in a slice"]
instance equalizer_left_isImmersion
    {S : Scheme.{u}} {X Y : Over S} (a b : X ⟶ Y) :
    IsImmersion (equalizer.ι a b).left := sorry

/-- Lemma 26.21.5: equalizer inclusions in a slice are canonically quasi-compact under a
quasi-separated target. -/
@[stacks 01KM "equalizer quasi-compactness"]
instance equalizer_quasiCompact
    {S : Scheme.{u}} {X Y : Over S} [QuasiSeparated Y.hom] (a b : X ⟶ Y) :
    QuasiCompact (equalizer.ι a b).left := sorry

end AlgebraicGeometry
