/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Specialization.LocallyConstant
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 59.75.5: on a scheme whose quasi-compact opens have finitely many
irreducible components (for example if the underlying space is Noetherian, or if
the scheme is locally Noetherian), a sheaf of sets on the small étale site is
finite locally constant if and only if every geometric stalk is finite and every
specialization map from the stalk at sbar to the stalk at tbar is bijective. -/
@[stacks 0GJ7] #check
  (AlgebraicGeometry.Scheme.finiteLocallyConstant_iff_finiteStalks_bijectiveSpecialization :
    ∀ {S : Scheme.{u}} [Scheme.HasFiniteIrreducibleComponentsOnCompactOpens S]
      [HasWeakSheafify S.smallEtaleTopology (Type u)]
      [∀ U : S.Etale, HasWeakSheafify (S.smallEtaleTopology.over U) (Type u)]
      (F : Sheaf S.smallEtaleTopology (Type u)),
      CategoryTheory.Sheaf.IsFiniteLocallyConstant F ↔
        (∀ sbar : Scheme.GeometricPoint S, Finite (Scheme.Etale.stalk sbar F.obj)) ∧
          Scheme.étaleSpecializationMapsBijective F)
