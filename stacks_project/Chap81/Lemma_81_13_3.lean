/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.Closed

/-!
# Lemma 81.13.3

In Situation 81.13.2, the kernel-pair coequalizer of `Y = X' ⨿ Z → X` exists
in algebraic spaces over `S`. The structure morphism `X₁ ⟶ X` is a finite
universal homeomorphism, an isomorphism over the complementary open `U`, and
the closed immersion `Z ⟶ X` lifts through `X₁`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing

variable {S : Scheme.{u}} {X X' Z : AlgebraicSpace S}

section

variable (f : X' ⟶ X) (i : Z ⟶ X) [IsLocallyNoetherian X]
  [IsClosedImmersion i] [Proper f]

/- Lemma 81.13.3: the kernel-pair coequalizer of `X' ⨿ Z ⟶ X` exists. -/
@[stacks 0AGI] #check
  (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.isCoequalizer
    (closedCoprodToAmbient f i) :
    ∀ {W : AlgebraicSpace S} (φ : closedCoprod f i ⟶ W),
      fst (closedCoprodToAmbient f i) ≫ φ =
        snd (closedCoprodToAmbient f i) ≫ φ →
      ∃! ψ : closedSpace f i ⟶ W, fromClosedCoprod f i ≫ ψ = φ)

#check (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.equalizes
  (closedCoprodToAmbient f i) :
  fst (closedCoprodToAmbient f i) ≫ fromClosedCoprod f i =
    snd (closedCoprodToAmbient f i) ≫ fromClosedCoprod f i)

#check (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.instIsFinite_toTarget
  (closedCoprodToAmbient f i) : IsFinite (closedSpaceToAmbient f i))

#check (AlgebraicGeometry.AlgebraicSpace.KernelPairCoequalizer.fromSource_comp_toTarget
  (closedCoprodToAmbient f i) :
  fromClosedCoprod f i ≫ closedSpaceToAmbient f i = closedCoprodToAmbient f i)

#check (AlgebraicGeometry.AlgebraicSpace.coproductι_desc
  ((fun b ↦ match b with
    | false => (f : closedFamily f i false ⟶ X)
    | true => (i : closedFamily f i true ⟶ X)) : ∀ b, closedFamily f i b ⟶ X) false :
  coproductι (closedFamily f i) false ≫ closedCoprodToAmbient f i = f)

#check (AlgebraicGeometry.AlgebraicSpace.coproductι_desc
  ((fun b ↦ match b with
    | false => (f : closedFamily f i false ⟶ X)
    | true => (i : closedFamily f i true ⟶ X)) : ∀ b, closedFamily f i b ⟶ X) true :
  coproductι (closedFamily f i) true ≫ closedCoprodToAmbient f i = i)

#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.closedLift_comp f i :
  closedLift f i ≫ closedSpaceToAmbient f i = i)

variable [IsIso (openInverseImageTo f (closedImmersionComplementι i))]

#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.universalHomeomorphism_closedSpaceToAmbient
  f i : UniversalHomeomorphism (closedSpaceToAmbient f i))

#check (AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing.isIsoOverOpen_closedSpaceToAmbient
  f i : IsIsoOverOpen (closedSpaceToAmbient f i) (closedImmersionComplementι i))

end

end AlgebraicGeometry.AlgebraicSpace.CoequalizerGlueing
