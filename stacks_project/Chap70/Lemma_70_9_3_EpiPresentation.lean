/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Presentation
public import Mathlib.CategoryTheory.Presentable.Finite
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap66.Definition_66_29_1_RingedSite

/-!
# Filtered colimit presentations with epimorphic transitions

If `X` is a quasi-compact quasi-separated algebraic space over a scheme `S`,
every finite-type quasi-coherent `𝒪_X`-module admits a small filtered colimit
presentation by finitely presented modules with epimorphic transition maps.
-/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- A finite-type quasi-coherent module on a quasi-compact quasi-separated algebraic space
admits a small filtered colimit presentation by finitely presented modules with epimorphic
transition maps. -/
theorem exists_finitePresentation_colimitPresentation_epi
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
      ∃ pres : ColimitPresentation I F,
        (∀ i : I, (pres.diag.obj i).IsFinitePresentation) ∧
          ∀ {i i' : I} (f : i ⟶ i'), Epi (pres.diag.map f) :=
  sorry

/-- A finite-type quasi-coherent module on a quasi-compact quasi-separated algebraic space
admits an epimorphism from a finitely presented module. -/
theorem exists_finitePresentation_epi
    {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
    [IsAbsolutelyQuasiSeparated X] (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent] :
    ∃ (G : X.Modules) (_ : G.IsFinitePresentation) (f : G ⟶ F), Epi f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
