/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Transitivity
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open SheafOfModules.RingedSite

universe u

/- Lemma 92.18.8. Composable homomorphisms of sheaves of rings have the canonical
cotangent transitivity distinguished triangle, without injectivity or flatness assumptions. -/
@[stacks 08SZ] #check (SheafOfModules.RingedSite.CotangentComplex.transitivityTriangle_distinguished :
  ∀ {D : Type u} [Category.{u} D] {J : GrothendieckTopology D}
    [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
    [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
    [HasWeakSheafify J CommRingCat.{u}]
    [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]
    [UnivLE.{u, u}]
    {A B C : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : B ⟶ C),
      SheafOfModules.RingedSite.CotangentComplex.transitivityTriangle φ ψ ∈
        distTriang (RingedSiteDerived J C))
