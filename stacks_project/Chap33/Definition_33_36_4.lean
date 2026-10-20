/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative

@[expose] public section

/-!
# Definition 33.36.4 compatibility entry point

The reusable relative-Frobenius target, map, and projection computations are
owned by `ReasLib.AlgebraicGeometry.Scheme.Frobenius.Relative`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

variable {p : ℕ} [Fact p.Prime]
variable {X S : Scheme.{u}} (f : X ⟶ S)
variable [Scheme.IsCharP S p]

/- Definition 33.36.4: the relative Frobenius is the morphism over `S` from `X` to the
pullback of `f` along the absolute Frobenius of `S`. -/
@[stacks 0CC9] #check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusOver (p := p) f :
    Over.mk f ⟶ AlgebraicGeometry.Scheme.Hom.relativeFrobeniusTargetOver (p := p) f)

#check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusTarget (p := p) f : Scheme.{u})

#check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusTarget_isPullback (p := p) f :
    IsPullback (pullback.fst f (Scheme.absoluteFrobenius p S))
      (AlgebraicGeometry.Scheme.Hom.relativeFrobeniusTargetOver (p := p) f).hom f
      (Scheme.absoluteFrobenius p S))

#check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_fst (p := p) f :
    -- Local instance justification (search instability): `f` canonically induces the characteristic on `X`, but global instance search cannot infer `f`.
    letI : Scheme.IsCharP X p :=
      AlgebraicGeometry.Scheme.Hom.isCharP_of_target (p := p) f
    AlgebraicGeometry.Scheme.Hom.relativeFrobenius (p := p) f ≫
        pullback.fst f (Scheme.absoluteFrobenius p S) =
      Scheme.absoluteFrobenius p X)

#check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_snd (p := p) f :
    AlgebraicGeometry.Scheme.Hom.relativeFrobenius (p := p) f ≫
        pullback.snd f (Scheme.absoluteFrobenius p S) = f)

#check
  (AlgebraicGeometry.Scheme.Hom.relativeFrobenius_unique (p := p) f :
    ∀ (g : X ⟶ AlgebraicGeometry.Scheme.Hom.relativeFrobeniusTarget (p := p) f),
      (
        -- Local instance justification (search instability): `f` canonically induces the characteristic on `X`, but global instance search cannot infer `f`.
        letI : Scheme.IsCharP X p :=
          AlgebraicGeometry.Scheme.Hom.isCharP_of_target (p := p) f
        g ≫ pullback.fst f (Scheme.absoluteFrobenius p S) =
          Scheme.absoluteFrobenius p X) →
      g ≫ pullback.snd f (Scheme.absoluteFrobenius p S) = f →
      g = AlgebraicGeometry.Scheme.Hom.relativeFrobenius (p := p) f)
