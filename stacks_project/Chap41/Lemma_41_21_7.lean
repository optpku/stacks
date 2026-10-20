/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.NormalCrossings.StrictHenselization
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 41.21.7: on a locally Noetherian J-2 or Nagata scheme, a closed subscheme
is a normal crossings divisor iff its pullback to every strict henselization at a point of its
support is a strict normal crossings divisor. -/
@[stacks 0CBS] #check
  (@AlgebraicGeometry.isNormalCrossingsDivisor_iff_strictHenselization.{u} :
    ∀ {X : Scheme.{u}} [IsLocallyNoetherian X] (D : X.IdealSheafData)
      (hX : Scheme.IsJ2 X ∨ Scheme.Nagata X),
        IsNormalCrossingsDivisor D ↔
          ∀ p : X, p ∈ D.support →
            ∀ (Rsh : Type u) [CommRing Rsh] [Algebra (X.presheaf.stalk p) Rsh]
              [IsStrictHenselizationOf (X.presheaf.stalk p) Rsh],
              letI : IsNoetherianRing Rsh :=
                @IsStrictHenselizationOf.isNoetherianRing
                  (X.presheaf.stalk p) _ _ Rsh _ _ _ _
              let g : Spec (CommRingCat.of Rsh) ⟶ X :=
                Spec.map (CommRingCat.ofHom (algebraMap (X.presheaf.stalk p) Rsh)) ≫
                  X.fromSpecStalk p
              IsStrictNormalCrossingsDivisor (D.comap g))
