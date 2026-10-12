/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.HomotopyColimit
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Support

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/-- On a quasi-compact quasi-separated scheme, a derived module supported on a closed subset
with quasi-compact complement is pseudo-coherent exactly when it has a sequential
homotopy-colimit presentation by perfect objects supported on that subset whose canonical maps
become isomorphisms after successively lower truncations. -/
theorem isPseudoCoherent_iff_exists_supported_perfect_homotopyColimit {X : Scheme.{u}}
    [CompactSpace X] [QuasiSeparatedSpace X]
    (T : TopologicalSpace.Closeds X) (hT : IsCompact (T.compl : Set X))
    (K : RingedSpace.ModuleDerived X.toRingedSpace)
    (hK_support : RingedSpace.ModuleDerived.IsSupportedOn K (T : Set X)) :
    RingedSpace.ModuleDerived.IsPseudoCoherent K ↔
      ∃ (Kseq : ℕ ⥤ RingedSpace.ModuleDerived X.toRingedSpace)
        (P : HomotopyColimit.Presentation Kseq K),
        ∀ n : ℕ,
          RingedSpace.ModuleDerived.IsPerfect (Kseq.obj n) ∧
            RingedSpace.ModuleDerived.IsSupportedOn (Kseq.obj n) (T : Set X) ∧
              IsIso ((t.truncGE (-((n : ℤ) + 1))).map (P.ι n)) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived
