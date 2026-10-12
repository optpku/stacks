/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion
public import ReasLib.RingTheory.Sequence.Regularity.Append
public import ReasLib.RingTheory.Sequence.QuasiRegular.Regularity

/-!
# Composition of regular immersions

Regular, Koszul-regular, and `H_1`-regular immersions are stable under
composition. Composing an `H_1`-regular immersion with a quasi-regular
immersion is quasi-regular.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

section

variable {X Y Z : Scheme.{u}} (i : Z ⟶ Y) (j : Y ⟶ X)

/-- The composite of two regular immersions is a regular immersion. -/
@[instance]
theorem isRegularImmersion_comp
    [IsRegularImmersion i] [IsRegularImmersion j] :
    IsRegularImmersion (i ≫ j) := sorry

/-- The composite of two Koszul-regular immersions is a Koszul-regular immersion. -/
@[instance]
theorem isKoszulRegularImmersion_comp
    [IsKoszulRegularImmersion i] [IsKoszulRegularImmersion j] :
    IsKoszulRegularImmersion (i ≫ j) := sorry

/-- The composite of two `H_1`-regular immersions is an `H_1`-regular immersion. -/
@[instance]
theorem isH1RegularImmersion_comp
    [IsH1RegularImmersion i] [IsH1RegularImmersion j] :
    IsH1RegularImmersion (i ≫ j) := sorry

/-- The composite of an `H_1`-regular immersion followed by a quasi-regular immersion is
quasi-regular. -/
@[instance]
theorem isQuasiRegularImmersion_comp_of_isH1RegularImmersion
    [IsH1RegularImmersion i] [IsQuasiRegularImmersion j] :
    IsQuasiRegularImmersion (i ≫ j) := sorry

end

end AlgebraicGeometry
