/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.ProEtale.StrictHenselization
import StacksCheckRecall

/-!
# Lemma 61.18.4

The spectrum of the strict henselization `𝒪_{S, s̄}^{sh}` is an object of the
small pro-étale site, and sections of a sheaf there recover the geometric stalk.
-/

open AlgebraicGeometry Scheme CategoryTheory Opposite

universe u

@[expose] public section

/- Lemma 61.18.4 (1): in the situation of Stacks 61.18, the scheme
`Spec(𝒪_{S, s̄}^{sh})` is an object of the small pro-étale site `S.ProEt`. -/
@[stacks 0993] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.strictHenselization :
    ∀ {S : Scheme.{u}} (s : GeometricPoint S), S.ProEt)

/- Lemma 61.18.4 (2): evaluation of a sheaf `F` on `S.ProEt` at
`Spec(𝒪_{S, s̄}^{sh})` is canonically isomorphic to the stalk `F_s̄`,
functorially in `F`. -/
@[stacks 0993] #check
  (AlgebraicGeometry.Scheme.GeometricPoint.sheafToPresheaf_toPresheafFiberNatTrans_isIso :
    ∀ {S : Scheme.{u}} (s : GeometricPoint S),
      IsIso
        (Functor.whiskerLeft (sheafToPresheaf (ProEt.topology S) (Type u))
          (GeometricPoint.toStalkNatTrans s)))
