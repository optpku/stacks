/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Order

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap66.Lemma_66_27_3_Space
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap68.Definition_68_11_7_HenselianLocalRing
public import stacks_project.Chap70.Lemma_70_19_3_Henselization
public import stacks_project.Chap71.Definition_71_10_9_Regular
public import stacks_project.Chap71.Lemma_71_10_7
public import stacks_project.Chap71.Lemma_71_10_10
public import stacks_project.Chap72.Definition_72_6_2_Prime

/-!
# Henselian pullback of meromorphic sections

Membership `s ∈ L_ξ` means some global section of `c_ξ^* L` sheafifies to the
identity-étale value of `pullbackMeromorphicSections c_ξ s`, where
`c_ξ = fromHenselization X ξ` and `L_ξ = (Modules.pullback c_ξ).obj L`. The
integer `ord_{Z, L}(s)` is the length difference of a nonzerodivisor
presentation of the ratio `s / s_ξ` in `Q(O_{X,ξ}^h)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory
open PresheafOfModules
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]

namespace MeromorphicSection

#check (AlgebraicGeometry.AlgebraicSpace.MeromorphicSection.ord_spec :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    [IsLocallyNoetherian X] [IsIntegral X] {L : X.Modules} [isInvertibleObject L]
    (s : meromorphicSections X L) (hs : IsRegularMeromorphicSection X L s)
    (Z : PrimeDivisor X) (a b : henselianLocalRing X Z.genericPoint)
    (ha : a ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hb : b ∈ nonZeroDivisors (henselianLocalRing X Z.genericPoint))
    (hrep : henselianFraction s hs Z =
      IsLocalization.mk' (FractionRing (henselianLocalRing X Z.genericPoint)) a ⟨b, hb⟩),
    ord s hs Z =
      ((Ring.ord (henselianLocalRing X Z.genericPoint) a).toNat : ℤ) -
        ((Ring.ord (henselianLocalRing X Z.genericPoint) b).toNat : ℤ))

end MeromorphicSection

end AlgebraicGeometry.AlgebraicSpace
