/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion

/-!
# Relative regular immersions of schemes

This file defines relative quasi-regular and relative `H_1`-regular immersions
by combining absolute regularity with flatness over the base.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X S Z : Scheme.{u}} {f : X ⟶ S} {i : Z ⟶ X}

/-- An immersion `i : Z ⟶ X` over `f : X ⟶ S` is relatively quasi-regular when `i`
is quasi-regular and the composite `i ≫ f : Z ⟶ S` is flat. -/
@[mk_iff]
class RelativeQuasiRegularImmersion (f : X ⟶ S) (i : Z ⟶ X) : Prop
    extends IsQuasiRegularImmersion i, Flat (i ≫ f)

/-- Absolute quasi-regularity together with flatness over the base canonically gives relative
quasi-regularity. -/
instance instRelativeQuasiRegularImmersion
    [IsQuasiRegularImmersion i] [Flat (i ≫ f)] :
    RelativeQuasiRegularImmersion f i := sorry

/-- An immersion `i : Z ⟶ X` over `f : X ⟶ S` is relatively `H_1`-regular when `i`
is `H_1`-regular and the composite `i ≫ f : Z ⟶ S` is flat. -/
@[mk_iff]
class RelativeH1RegularImmersion (f : X ⟶ S) (i : Z ⟶ X) : Prop
    extends IsH1RegularImmersion i, Flat (i ≫ f)

/-- Absolute `H_1`-regularity together with flatness over the base canonically gives relative
`H_1`-regularity. -/
instance instRelativeH1RegularImmersion
    [IsH1RegularImmersion i] [Flat (i ≫ f)] :
    RelativeH1RegularImmersion f i := sorry

end

end AlgebraicGeometry
