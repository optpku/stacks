/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.Gysin.ClosedImmersion.Differential
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite Scheme.Hom
  Scheme.Hom.LocalCohomology
open AlgebraicGeometry.Scheme.DeRham.Gysin

/-Lemma 50.23.4: compatibility with the relative de Rham differentials.-/
@[stacks 0G87]
#check (@AlgebraicGeometry.Scheme.DeRham.Gysin.mapOfClosedImmersion_d :
  ∀ {Z X S : AlgebraicGeometry.Scheme} (i : Z ⟶ X) [IsClosedImmersion i]
    [Scheme.Hom.FinitePresentation i] (f : X ⟶ S) (c p : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank c (Scheme.Hom.conormalSheaf i)]
    (P : EquationPresentation i c),
    (@Abelian.epiDesc _ _ _ _ _ (equationGysinSourceComparison i f c p P)
          (equationGysinSourceComparison_epi i f c p P) _
          ((forget₂ _ _).map
              (((Scheme.Modules.pushforward i).map
                (pullbackFormToClosedForm i f p)).val.app (op P.carrier)) ≫
            (forget₂ _ _).map
              ((mapOfClosedImmersion i f c p).val.app (op P.carrier)) ≫
            @inv _ _ _ _ (equationGysinTargetComparison i f c (p + c) P)
              (equationGysinTargetComparison_isIso i f c (p + c) P))
          (mapOfClosedImmersion_killsEquationSourceKernel i f c p P)) ≫
        (forget₂ _ _).map
          ((targetDifferential (P.carrier.ι ≫ f) P.generators (p + c)).val.app (op ⊤)) =
      (forget₂ _ _).map
          ((sourceDifferential (P.carrier.ι ≫ f) P.generators p).val.app (op ⊤)) ≫
        (@Abelian.epiDesc _ _ _ _ _ (equationGysinSourceComparison i f c (p + 1) P)
          (equationGysinSourceComparison_epi i f c (p + 1) P) _
          ((forget₂ _ _).map
              (((Scheme.Modules.pushforward i).map
                (pullbackFormToClosedForm i f (p + 1))).val.app (op P.carrier)) ≫
            (forget₂ _ _).map
              ((mapOfClosedImmersion i f c (p + 1)).val.app (op P.carrier)) ≫
            @inv _ _ _ _ (equationGysinTargetComparison i f c ((p + 1) + c) P)
              (equationGysinTargetComparison_isIso i f c ((p + 1) + c) P))
          (mapOfClosedImmersion_killsEquationSourceKernel i f c (p + 1) P)) ≫
        (forget₂ _ _).map
          ((eqToHom (congrArg (restrictedTarget (P.carrier.ι ≫ f) P.generators)
            (Nat.add_right_comm p 1 c))).val.app (op ⊤)))
