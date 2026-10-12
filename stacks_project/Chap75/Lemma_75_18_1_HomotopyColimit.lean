/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Definition
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact
public import stacks_project.Chap75.Definition_75_14_1_PerfectApproximation

/-!
# Sequential homotopy colimits of perfect complexes

On a quasi-compact quasi-separated algebraic space, pseudo-coherence of an object of
`D(𝒪_X)` is equivalent to the existence of a sequential homotopy-colimit presentation by
perfect objects whose canonical maps become isomorphisms after successively lower
truncations.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

/-- On a quasi-compact quasi-separated algebraic space, a derived module is pseudo-coherent
exactly when it has a sequential homotopy-colimit presentation by perfect objects whose
canonical maps become isomorphisms after successively lower truncations. -/
theorem isPseudoCoherent_iff_exists_perfect_homotopyColimit {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (K : ModuleDerived X) :
    IsPseudoCoherent X K ↔
      ∃ (Kseq : ℕ ⥤ ModuleDerived X) (P : HomotopyColimit.Presentation Kseq K),
        ∀ n : ℕ,
          IsPerfect (Kseq.obj n) ∧
            IsIso ((t.truncGE (-((n : ℤ) + 1))).map (P.ι n)) := sorry

/-- A sequential homotopy colimit of perfect derived modules, with canonical maps becoming
isomorphisms after successively lower truncations, is pseudo-coherent. -/
theorem isPseudoCoherent_of_perfect_homotopyColimit {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
    (K : ModuleDerived X) (Kseq : ℕ ⥤ ModuleDerived X)
    (P : HomotopyColimit.Presentation Kseq K)
    (h : ∀ n : ℕ,
      IsPerfect (Kseq.obj n) ∧ IsIso ((t.truncGE (-((n : ℤ) + 1))).map (P.ι n))) :
    IsPseudoCoherent X K := sorry

/-- A pseudo-coherent derived module on a quasi-compact quasi-separated algebraic space
admits a sequential homotopy-colimit presentation by perfect objects whose canonical maps
become isomorphisms after successively lower truncations. -/
theorem exists_perfect_homotopyColimit {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] (K : ModuleDerived X)
    (hK : IsPseudoCoherent X K) :
    ∃ (Kseq : ℕ ⥤ ModuleDerived X) (P : HomotopyColimit.Presentation Kseq K),
      ∀ n : ℕ,
        IsPerfect (Kseq.obj n) ∧
          IsIso ((t.truncGE (-((n : ℤ) + 1))).map (P.ι n)) := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
