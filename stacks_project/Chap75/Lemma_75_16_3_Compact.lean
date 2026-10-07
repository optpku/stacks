module

public import Mathlib.Topology.Sets.Closeds
public import ReasLib.CategoryTheory.Preadditive.CompactObject
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap67.Definition_67_8_2_QuasiCompact
public import stacks_project.Chap67.Remark_67_12_5_Opens
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation
public import stacks_project.Chap81.Lemma_81_10_10_SupportedOn

/-!
# Compact and perfect supported quasicoherent complexes

Compact objects in `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated algebraic
space, for a closed subset `T` with quasi-compact complement, are characterized by
perfectness in `D(𝒪_X)`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn

/-- An object of `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated algebraic space,
for a closed subset `T` whose complement is quasi-compact, is compact if and only if its
underlying derived module is perfect. -/
theorem isCompactObject_iff_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl))
    (E : SupportedOn X (T : Set (Points X))) :
    IsCompactObject E ↔ ModuleDerived.IsPerfect E.obj := sorry

/-- A perfect object of `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated algebraic
space, for a closed subset `T` whose complement is quasi-compact, is compact. -/
theorem isCompactObject_of_isPerfect {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl))
    {E : SupportedOn X (T : Set (Points X))} (hE : ModuleDerived.IsPerfect E.obj) :
    IsCompactObject E := sorry

/-- A compact object of `D_QCoh,T(𝒪_X)` on a quasi-compact and quasi-separated algebraic
space, for a closed subset `T` whose complement is quasi-compact, has a perfect
underlying derived module. -/
theorem isPerfect_of_isCompactObject {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (T : Closeds (Points X))
    (hT : QuasiCompact (OpenSubspace.ofOpensι T.compl))
    {E : SupportedOn X (T : Set (Points X))} (hE : IsCompactObject E) :
    ModuleDerived.IsPerfect E.obj := sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn
