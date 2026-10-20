/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pushforward.Counterexamples

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Lemma 110.30.1 -/
@[stacks 078D] #check (AlgebraicGeometry.Scheme.Modules.pushforward.qcqs_hypotheses_are_necessary :
  ∀ (k : Type u) [Field k],
    (IsSeparated AlgebraicGeometry.Scheme.Modules.pushforward.InfiniteCoproduct.hom ∧
      ¬ QuasiCompact AlgebraicGeometry.Scheme.Modules.pushforward.InfiniteCoproduct.hom ∧
      (SheafOfModules.unit AlgebraicGeometry.Scheme.Modules.pushforward.InfiniteCoproduct.scheme.ringCatSheaf).IsQuasicoherent ∧
      ¬ ((Scheme.Modules.pushforward AlgebraicGeometry.Scheme.Modules.pushforward.InfiniteCoproduct.hom).obj
        (SheafOfModules.unit AlgebraicGeometry.Scheme.Modules.pushforward.InfiniteCoproduct.scheme.ringCatSheaf)).IsQuasicoherent) ∧
    (QuasiCompact (AlgebraicGeometry.Scheme.Modules.pushforward.GluedCopies.hom k) ∧
      ¬ QuasiSeparated (AlgebraicGeometry.Scheme.Modules.pushforward.GluedCopies.hom k) ∧
      (SheafOfModules.unit (AlgebraicGeometry.Scheme.Modules.pushforward.GluedCopies.scheme k).ringCatSheaf).IsQuasicoherent ∧
      ¬ ((Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.Modules.pushforward.GluedCopies.hom k)).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.Modules.pushforward.GluedCopies.scheme k).ringCatSheaf)).IsQuasicoherent))
