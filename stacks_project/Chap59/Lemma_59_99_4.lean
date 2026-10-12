/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap59.Lemma_59_99_4_Adjunction
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig

noncomputable section

universe u

/- Lemma 59.99.4: for a scheme `S` and `K` in the derived category of abelian
sheaves on the small étale site, the derived adjunction unit
`K ⟶ Rπ_{S,*} (π_S⁻¹ K)` is an isomorphism. -/
@[stacks 0DDI] #check
  (AlgebraicGeometry.Scheme.Etale.SmallToBig.etalePiDerivedAdjunction_unit_isIso :
    ∀ (S : Scheme.{u})
      [HasSheafify S.smallEtaleTopology AddCommGrpCat.{u}]
      [HasSheafify (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u}]
      [Abelian (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
      [Abelian (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
      [HasDerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})]
      [HasDerivedCategory
        (Sheaf (S.overGrothendieckTopology @Etale) AddCommGrpCat.{u})]
      [∀ P : S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u},
        (relocalizationFunctor (𝟙 S)).op.HasLeftKanExtension P]
      [PreservesFiniteLimits
        ((relocalizationFunctor (𝟙 S)).op.lan :
          (S.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤
            ((Over S)ᵒᵖ ⥤ AddCommGrpCat.{u}))]
      (K : DerivedCategory (Sheaf S.smallEtaleTopology AddCommGrpCat.{u})),
      IsIso ((etalePiDerivedAdjunction S).unit.app K))
