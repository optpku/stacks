/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.CohomologyBaseChange.InternalHomPushforward

/-! # Internal-Hom pushforward base change for relatively flat complexes -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits
open CategoryTheory.DerivedCategory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed ComplexShape

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

variable {S : Scheme.{u}} {X' X Y' Y : AlgebraicSpace S}

/- Lemma 75.21.5 (1): internal-Hom pushforward base change for
a perfect derived module and a bounded-above relatively flat complex. -/
@[stacks 08JQ] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardInternalHomBaseChange_isIso_of_isPerfect :
  ∀
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (hE : ModuleDerived.IsPerfect E)
    (hG_minus : CochainComplex.minus (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x),
    IsIso (internalHomPushforwardBaseChange g' f' f g sq E G))

/- Lemma 75.21.5 (2): internal-Hom pushforward base change for
a pseudo-coherent derived module and a bounded relatively flat complex. -/
@[stacks 08JQ] #check (AlgebraicGeometry.AlgebraicSpace.DerivedQCoh.pushforwardInternalHomBaseChange_isIso_of_isPseudoCoherent :
  ∀
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (sq : IsPullback g' f' f g) (E : ModuleDerived X)
    (G : CochainComplex (Modules X) ℤ) (hE : IsPseudoCoherent X E)
    (hG_bounded : CochainComplex.bounded (Modules X) G)
    (hG_qcoh : ∀ n : ℤ, (G.X n).IsQuasicoherent)
    (hG_flat : ∀ n : ℤ, ∀ x, Modules.flatOverAt (G.X n) f x),
    IsIso (internalHomPushforwardBaseChange g' f' f g sq E G))

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
