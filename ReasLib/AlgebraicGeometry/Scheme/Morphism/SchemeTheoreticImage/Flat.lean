/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

/-!
# Flat base change of scheme-theoretic images

Kernel ideal sheaves and scheme-theoretic images commute with flat base change for
quasi-compact morphisms of schemes.
-/

@[expose] public section

open CategoryTheory Limits
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y V : Scheme.{u}}

/-- The kernel ideal sheaf of a quasi-compact morphism commutes with flat base change. -/
theorem ker_pullback_snd_of_flat
    (f : X ⟶ Y) [Flat f] (g : V ⟶ Y) [QuasiCompact g] :
    (pullback.snd g f).ker = g.ker.comap f := sorry

/-- The scheme-theoretic image of a quasi-compact morphism commutes with flat base change. -/
theorem image_pullback_snd_of_flat
    (f : X ⟶ Y) [Flat f] (g : V ⟶ Y) [QuasiCompact g] :
    Scheme.Hom.image (pullback.snd g f) = (g.ker.comap f).subscheme := sorry

end AlgebraicGeometry.Scheme.Hom
