/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.RingTheory.Henselian.Henselization.Completion
public import ReasLib.RingTheory.Henselian.Henselization.Reduced
public import ReasLib.RingTheory.AdicCompletion.AnalyticallyUnramified.ReducedCompletion
import StacksCheckRecall

@[expose] public section

open IsLocalRing
open scoped AlgebraicGeometry

universe u v

section

variable (S : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian S]
variable (s : S) (Rh : Type v) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
variable [IsHenselizationOf (S.presheaf.stalk s) Rh]

/- Remark 59.33.4 (1): for a locally Noetherian scheme, the henselization of a stalk is
Noetherian. -/
@[stacks 03QM]
#check (IsHenselizationOf.isNoetherianRing (R := S.presheaf.stalk s) :
  IsNoetherianRing Rh)

/- Remark 59.33.4 (2): the maximal-ideal completions of a stalk and its henselization are
canonically identified over a locally Noetherian scheme. -/
@[stacks 03QM]
#check (IsHenselizationOf.Completion.map_bijective :
  Function.Bijective
    (IsHenselizationOf.Completion.map :
      AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s) →+*
        AdicCompletion (maximalIdeal Rh) Rh))

/- Remark 59.33.4 (3): the structural map from a stalk to its henselization is injective,
giving the first inclusion in the displayed chain. -/
@[stacks 03QM]
#check (IsHenselizationOf.injective (R := S.presheaf.stalk s) (S := Rh) :
  Function.Injective (algebraMap (S.presheaf.stalk s) Rh))

/- Remark 59.33.4 (4a): the henselization admits a unique comparison map to the stalk
completion. -/
@[stacks 03QM]
#check (IsHenselizationOf.Completion.existsUnique_comparison :
  ∃! iota : Rh →ₐ[S.presheaf.stalk s]
    AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s),
    IsHenselizationOf.Completion.IsComparison iota)

/- Remark 59.33.4 (4b): each comparison to the stalk completion is injective,
giving the second inclusion in the displayed chain. -/
@[stacks 03QM]
#check (IsHenselizationOf.Completion.Comparison.injective :
  ∀ iota : IsHenselizationOf.Completion.Comparison (R := S.presheaf.stalk s) (Rh := Rh),
    Function.Injective iota.toAlgHom)

/- Remark 59.33.4 (5): reducedness of a locally Noetherian stalk passes to its
henselization. -/
@[stacks 03QM]
#check ((IsHenselizationOf.isReduced_iff (R := S.presheaf.stalk s) (S := Rh)).mp :
  IsReduced (S.presheaf.stalk s) → IsReduced Rh)

end

/- Remark 59.33.4 (6): in general a reduced Noetherian local ring can have a
nonreduced maximal-ideal completion. -/
@[stacks 03QM]
#check (IsAnalyticallyUnramified.exists_reduced_with_nonreduced_completion :
  ∃ (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A) (_ : IsLocalRing A),
    IsReduced A ∧ ¬ IsReduced (AdicCompletion (maximalIdeal A) A))
