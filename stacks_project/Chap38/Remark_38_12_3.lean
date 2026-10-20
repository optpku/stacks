/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.Devissage.CompleteAt.Decomposition
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CommRingCat
open scoped DirectSum

universe u

/- Remark 38.12.3: the conclusion of Lemma 38.12.2 remains valid when flatness is
assumed only at a chosen prime `q` over `r`, provided a complete dévissage at `q` is given. -/
@[stacks 05IC] #check
  (Module.Devissage.CompleteAt.existsAwayDecomposition :
    ∀ {R : Type u} [CommRing R]
      {S : FGAlgCat.{u} R} [Algebra.FinitePresentation R S.obj]
      {N : FGModuleCat.{u} S.obj} [Module R N] [IsScalarTower R S.obj N]
        [Module.FinitePresentation S.obj N]
      {r : PrimeSpectrum R} {q : PrimeSpectrum S.obj}
      {hq : r.asIdeal = q.asIdeal.comap (algebraMap R S.obj)}
      (D : Module.Devissage.CompleteAt R S N r q hq),
      q ∈ Module.flatOverBaseLocus R S.obj N →
      ∃ f : R, f ∉ r.asIdeal ∧
        Nonempty
          (LocalizedModule.Away f N ≃ₗ[R]
            ⨁ i : Fin (D.toComplete.last + 1),
              (Fin (D.toComplete.stage i).rank →
                Localization.Away (algebraMap R (D.toComplete.stage i).B f))) ∧
        (∀ i : Fin (D.toComplete.last + 1),
          (Localization.awayMap (algebraMap R (D.toComplete.stage i).B) f).Smooth ∧
            GeometricallyIrreducible
              (Spec.map
                (ofHom (Localization.awayMap (algebraMap R (D.toComplete.stage i).B) f)))) ∧
        Module.Projective (Localization.Away f) (LocalizedModule.Away f N))
