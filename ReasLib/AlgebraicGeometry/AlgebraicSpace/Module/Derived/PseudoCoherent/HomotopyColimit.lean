module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Presentation.Definition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Perfect
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.PseudoCoherent

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

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
