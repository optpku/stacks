/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Meromorphic.Order

/-!
# Tensor additivity of meromorphic section orders

Orders are computed in henselian local rings of algebraic spaces. Generalizing
these orders to arbitrary ringed sites requires corresponding divisor theory.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.MeromorphicSection

variable {S : Scheme.{u}} {X : AlgebraicSpace S}
variable [IsLocallyNoetherian X] [IsIntegral X]

/-- The henselian order of a tensor of regular meromorphic sections along a prime
divisor is the sum of their orders, independently of the local generators. -/
theorem ord_tensor {L N : X.Modules} [isInvertibleObject L] [isInvertibleObject N]
    (s : meromorphicSections X L) (t : meromorphicSections X N)
    (hs : IsRegularMeromorphicSection X L s)
    (ht : IsRegularMeromorphicSection X N t) (Z : PrimeDivisor X) :
    ord (meromorphicSectionTensor s t) (isRegularMeromorphicSection_tensor s t hs ht) Z =
      ord s hs Z + ord t ht Z := sorry

end AlgebraicGeometry.AlgebraicSpace.MeromorphicSection
