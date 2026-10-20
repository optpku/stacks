/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Transitivity
public import stacks_project.Chap92.Definition_92_22_1_Cotangent
public import stacks_project.Chap92.Lemma_92_18_7_Functoriality

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open SheafOfModules.RingedSite

universe u

/- The canonical transitivity triangle of cotangent complexes of ring sheaves. -/
#check (SheafOfModules.RingedSite.CotangentComplex.transitivityTriangle :
  ∀ {D : Type u} [Category.{u} D] {J : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify J CommRingCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
    [UnivLE.{u, u}]
    {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C),
      CategoryTheory.Pretriangulated.Triangle (RingedSiteDerived J C))
