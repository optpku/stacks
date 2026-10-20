/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Impurity.Henselization

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

/- Remark 38.16.2 (1): for a locally finite type morphism and a finite type quasicoherent
module, the absence of elementary impurities above `s` is equivalent to the absence of
impurities whose base-change morphism is quasi-finite at the special point. -/
@[stacks 05J5] #check
  (AlgebraicGeometry.Scheme.Modules.Impurity.noElementary_iff_noQuasiFiniteAt :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (s : S),
      (∀ I : AlgebraicGeometry.Scheme.Modules.Impurity F f s, ¬ I.IsElementary) ↔
        ¬ ∃ I : AlgebraicGeometry.Scheme.Modules.Impurity F f s,
          AlgebraicGeometry.Scheme.Hom.FiniteType.QuasiFiniteAt I.g I.specialPoint)

/- Remark 38.16.2 (2): over a chosen henselization of `S` at `s`, absence of impurities
is equivalent to every relative associated point specializing to the closed fibre. -/
@[stacks 05J5] #check
  (AlgebraicGeometry.Scheme.Modules.Impurity.noHenselianImpurity_iff_specializes_closedFiber :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (F : X.Modules) (f : X ⟶ S)
      [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType] (s : S)
      (Rh : Type u) [CommRing Rh] [Algebra (S.presheaf.stalk s) Rh]
      [IsHenselizationOf (S.presheaf.stalk s) Rh],
      IsEmpty (AlgebraicGeometry.Scheme.Modules.Impurity.Over F f s
        (AlgebraicGeometry.Scheme.Henselization.map S s Rh) (IsLocalRing.closedPoint Rh)) ↔
        ∀ x ∈ AlgebraicGeometry.Scheme.Modules.relativeAssassin
            (Limits.pullback.snd f (AlgebraicGeometry.Scheme.Henselization.map S s Rh))
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (Limits.pullback.fst f
                (AlgebraicGeometry.Scheme.Henselization.map S s Rh))).obj F),
          ∃ y, Specializes x y ∧
            Limits.pullback.snd f (AlgebraicGeometry.Scheme.Henselization.map S s Rh) y =
              IsLocalRing.closedPoint Rh)
