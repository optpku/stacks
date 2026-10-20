/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.Conditions

/-!
# Finite local freeness criteria for scheme modules

For a quasi-coherent module on a scheme, this leaf records the standard equivalence between
finite local freeness and the flat, stalkwise-free, and locally-free formulations.  The named
`_iff_isFiniteLocallyFree` bridges are intended for ordinary downstream use; consumers should not
need to manipulate `List.TFAE` directly.
-/

@[expose] public section

open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- For a quasi-coherent scheme module `ℱ`, finite local freeness is equivalent to
finite-presentation flatness, finite presentation with free stalks, local freeness of finite type,
and finite type with free stalks and locally constant fiber rank. -/
@[stacks 05P2]
theorem finiteLocallyFree_tfae (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    List.TFAE [
      FinitePresentationFlat ℱ,
      FinitePresentationStalkwiseFree ℱ,
      LocallyFreeFiniteType ℱ,
      SheafOfModules.IsFiniteLocallyFree ℱ,
      FiniteTypeStalkwiseFreeRankLocallyConstant ℱ
    ] := sorry

/-- Under quasi-coherence, finite-presentation flatness is equivalent to finite local freeness. -/
theorem finitePresentationFlat_iff_isFiniteLocallyFree
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    FinitePresentationFlat ℱ ↔
      SheafOfModules.IsFiniteLocallyFree ℱ := sorry

/-- Under quasi-coherence, finite presentation with free stalks is equivalent to finite local
freeness. -/
theorem finitePresentationStalkwiseFree_iff_isFiniteLocallyFree
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    FinitePresentationStalkwiseFree ℱ ↔
      SheafOfModules.IsFiniteLocallyFree ℱ := sorry

/-- Under quasi-coherence, local freeness of finite type is equivalent to finite local freeness. -/
theorem locallyFreeFiniteType_iff_isFiniteLocallyFree
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    LocallyFreeFiniteType ℱ ↔
      SheafOfModules.IsFiniteLocallyFree ℱ := sorry

/-- Under quasi-coherence, finite type with free stalks and locally constant fiber rank is
equivalent to finite local freeness. -/
theorem finiteTypeStalkwiseFreeRankLocallyConstant_iff_isFiniteLocallyFree
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] :
    FiniteTypeStalkwiseFreeRankLocallyConstant ℱ ↔
      SheafOfModules.IsFiniteLocallyFree ℱ := sorry

end AlgebraicGeometry.Scheme.Modules
