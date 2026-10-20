/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.ClosedSubset.Perfect.TensorAnnihilator
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory
open DerivedCategory.TStructure TopologicalSpace

universe u

/- Lemma 75.16.5 -/
@[stacks 0AEE] #check
  (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.existsTensorAnnihilator :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
      [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X]
      (T : Closeds (Points X)),
      QuasiCompact ((OpenSubspace.fromOpens T.compl).ι) →
        ∀ (P : DerivedQCoh X)
          (E : AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn X
            (T : Set (Points X)))
          (α : P ⟶
            (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.SupportedOn.inclusion X
              (T : Set (Points X))).obj E),
          ModuleDerived.IsPerfect P.obj ∨
              (IsPseudoCoherent X P.obj ∧
                (t.plus : ObjectProperty (ModuleDerived X)) E.obj) →
            ∃ (I : ModuleDerived X) (i : I ⟶ (DerivedQCoh.structureSheaf X).obj),
              ModuleDerived.IsPerfect I ∧
                ((ModuleDerived.tensorBifunctor X).map (Prod.mkHom i (𝟙 P.obj))) ≫
                  ModuleDerived.tensorLeftUnitor P.obj ≫
                  (DerivedQCoh.inclusion X).map α = 0 ∧
                IsIso ((ModuleDerived.pullback ((OpenSubspace.fromOpens T.compl).ι)).map i))

