module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.HomotopyColimit
public import stacks_project.Chap36.Lemma_36_10_1_PseudoCoherent

@[expose] public section

open AlgebraicGeometry CategoryTheory
open DerivedCategory.TStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived

/- Lemma 36.19.1: on a quasi-compact quasi-separated scheme, a derived module is
pseudo-coherent exactly when it has a sequential homotopy-colimit presentation by perfect
objects whose canonical maps become isomorphisms after successively lower truncations. -/
@[stacks 0DJN] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.isPseudoCoherent_iff_exists_perfect_homotopyColimit :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (K : RingedSpace.ModuleDerived X.toRingedSpace),
      RingedSpace.ModuleDerived.IsPseudoCoherent K ↔
        ∃ (Kseq : ℕ ⥤ RingedSpace.ModuleDerived X.toRingedSpace)
          (P : HomotopyColimit.Presentation Kseq K),
          ∀ n : ℕ,
            RingedSpace.ModuleDerived.IsPerfect (Kseq.obj n) ∧
              IsIso ((t.truncGE (-((n : ℤ) + 1))).map (P.ι n)))

end AlgebraicGeometry.Scheme.ModuleDerived
