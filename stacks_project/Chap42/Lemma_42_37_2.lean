/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowGroup.ProjectiveBundle.ChernClass.RankOne

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula

open Scheme.Modules.MeromorphicSection

/- Lemma 42.37.2: The first Chern class of a rank-one finite locally free module
on an integral scheme is its associated relative divisor class. -/
@[stacks 02U2]
#check
  (AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula.firstChernClass_eq_relativeDivisorClass :
    ∀ {S X P : Scheme.{u}} (δ : S → ℤ) (p : X ⟶ S)
      [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType p]
      [IsIntegral X] (ℒ : X.Modules) [Scheme.Modules.IsFiniteLocallyFreeOfRank 1 ℒ]
      (π : P ⟶ X) (hπ : Scheme.ProjectiveBundle.Representation π ℒ)
      [LocallyOfFiniteType (π ≫ p)] (n : ℤ)
      (hn : p.relativeDimensionFunction δ (genericPoint X) = n)
      (F : ChowGroup.ProjectiveBundleFormula δ p ℒ 1 π hπ n hn)
      (hF : F.IsGeometric δ p ℒ 1 π hπ n hn)
      (s : X.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0),
      F.chernClass δ p ℒ 1 π hπ n hn (1 : Fin 2) =
        @relativeDivisorClass S X p inferInstance
          inferInstance δ inferInstance inferInstance ℒ
          (SheafOfModules.RingedSite.rankOne_isInvertible ℒ)
          s hs (n - 1) (hn.trans (sub_add_cancel n 1).symm))

end AlgebraicGeometry.ChowGroup.ProjectiveBundleFormula
