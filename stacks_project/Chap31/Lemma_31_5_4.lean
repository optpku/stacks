/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.WeaklyAssociatedPoints.ExactSequence

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {S : ShortComplex X.Modules}

/-- Lemma 31.5.4 (1): in a short exact complex of quasi-coherent modules on a scheme, every
weakly associated point of the middle term is weakly associated to the left or right term. -/
@[stacks 05AN]
theorem weakAss_middle_subset_union_of_shortExact_of_isQuasicoherent
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    S.X₂.weakAss ⊆ S.X₁.weakAss ∪ S.X₃.weakAss :=
  AlgebraicGeometry.Scheme.Modules.weakAss_middle_subset_union_of_shortExact hS

/-- Lemma 31.5.4 (2): in a short exact complex of quasi-coherent modules on a scheme, every
weakly associated point of the left term is weakly associated to the middle term. -/
@[stacks 05AN]
theorem weakAss_left_subset_of_shortExact_of_isQuasicoherent
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (hS : S.ShortExact) :
    S.X₁.weakAss ⊆ S.X₂.weakAss :=
  AlgebraicGeometry.Scheme.Modules.weakAss_left_subset_of_shortExact hS

end AlgebraicGeometry.Scheme.Modules
