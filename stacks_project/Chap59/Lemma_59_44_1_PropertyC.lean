/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SmallToBig
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PropertyC

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SmallToBig

universe u

export AlgebraicGeometry.Scheme.Etale.SmallToBig
  (hasPropertyC hasPropertyC_iff smallEtalePullback_isCoverDense_of_hasPropertyC)

#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.hasPropertyC :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), Prop)

#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.hasPropertyC_iff :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
    hasPropertyC f ↔
      ∀ (U : X.Etale),
        ∃ (V : Y.Etale) (h : pullback f V.hom ⟶ U.left),
          Surjective h ∧ h ≫ U.hom = pullback.fst f V.hom)

#check (AlgebraicGeometry.Scheme.Etale.SmallToBig.smallEtalePullback_isCoverDense_of_hasPropertyC :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (hC : hasPropertyC f),
    (Scheme.smallEtalePullback f).IsCoverDense X.smallEtaleTopology)
