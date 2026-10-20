/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.SectionSequence.Regularity
import StacksCheckRecall

universe u

open Opposite TopologicalSpace

/- Lemma 31.20.1 (1): a regular finite family of global sections on a ringed space is
Koszul-regular. -/
@[stacks 063C] #check
  (AlgebraicGeometry.RingedSpace.SectionSequence.IsRegular.isKoszulRegular :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}} {r : ℕ}
      {f : Fin r → X.presheaf.obj (op (⊤ : Opens X))},
      AlgebraicGeometry.RingedSpace.SectionSequence.IsRegular f →
        AlgebraicGeometry.RingedSpace.SectionSequence.IsKoszulRegular f)

/- Lemma 31.20.1 (2): a Koszul-regular finite family of global sections on a ringed space is
`H₁`-regular. -/
@[stacks 063C]
#check
  (AlgebraicGeometry.RingedSpace.SectionSequence.IsKoszulRegular.isH1Regular :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}} {r : ℕ}
      {f : Fin r → X.presheaf.obj (op (⊤ : Opens X))},
      AlgebraicGeometry.RingedSpace.SectionSequence.IsKoszulRegular f →
        AlgebraicGeometry.RingedSpace.SectionSequence.IsH1Regular f)

/- Lemma 31.20.1 (3): an `H₁`-regular finite family of global sections on a ringed space is
quasi-regular. -/
@[stacks 063C]
#check
  (AlgebraicGeometry.RingedSpace.SectionSequence.IsH1Regular.isQuasiRegular :
    ∀ {X : AlgebraicGeometry.RingedSpace.{u}} {r : ℕ}
      {f : Fin r → X.presheaf.obj (op (⊤ : Opens X))},
      AlgebraicGeometry.RingedSpace.SectionSequence.IsH1Regular f →
        AlgebraicGeometry.RingedSpace.SectionSequence.IsQuasiRegular f)
