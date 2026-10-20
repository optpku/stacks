/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Henselization
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules.Impurity

/- Lemma 38.15.7: if an impurity of `F` above `s` exists over the spectrum of a chosen
henselization of the stalk at `s`, then `F` has an impurity above `s` whose pointed base
change is an elementary étale neighbourhood. -/
@[stacks 05J2] #check
  (AlgebraicGeometry.Scheme.Modules.Impurity.exists_elementary_of_henselization :
    ∀ {X S : Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [Hom.FiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
      (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
      [IsHenselizationOf (S.presheaf.stalk s) Rh]
      (h_impurity : Nonempty
        (Over F f s (Scheme.Henselization.map S s Rh) (IsLocalRing.closedPoint Rh))),
      ∃ I : Impurity F f s, I.IsElementary)

end AlgebraicGeometry.Scheme.Modules.Impurity
