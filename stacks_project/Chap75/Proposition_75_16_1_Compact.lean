module

public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_5_1_DerivedQCoh
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

/-!
# Compact and perfect quasicoherent complexes on algebraic spaces

Compact objects in `D_QCoh(𝒪_X)` on a quasi-compact and quasi-separated algebraic space
are characterized by perfectness.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- An object of the derived category of quasicoherent modules on a quasi-compact and
quasi-separated algebraic space is compact if and only if its underlying derived module is
perfect. -/
theorem isCompactObject_iff_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (E : DerivedQCoh X) :
    IsCompactObject E ↔ ModuleDerived.IsPerfect E.obj := sorry

/-- A perfect object of the derived category of quasicoherent modules on a quasi-compact and
quasi-separated algebraic space is compact. -/
theorem isCompactObject_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {E : DerivedQCoh X}
    (hE : ModuleDerived.IsPerfect E.obj) : IsCompactObject E := sorry

/-- A compact object of the derived category of quasicoherent modules on a quasi-compact and
quasi-separated algebraic space has a perfect underlying derived module. -/
theorem isPerfect_of_isCompactObject {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] {E : DerivedQCoh X}
    (hE : IsCompactObject E) : ModuleDerived.IsPerfect E.obj := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
