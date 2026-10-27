/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Fundamental
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom AlgebraicGeometry.BivariantClass

universe u

/- Lemma 42.62.2 (1): for a smooth scheme of constant dimension `d` over a field,
cap with the fundamental class identifies degree-`p` operational Chow cohomology with
Chow homology in degree `d - p`. -/
@[stacks 0FC2] #check (AlgebraicGeometry.BivariantClass.capFundamentalEquiv :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p : ℤ),
    BivariantClass.group (fun _ ↦ 0) (𝟙 X) p ≃+
      RelativeChow (fun _ ↦ 0) X ((d : ℤ) - p))

/- Lemma 42.62.2 (2): fundamental-class cap carries composition of bivariant classes
to the diagonal intersection product. -/
@[stacks 0FC2] #check (AlgebraicGeometry.BivariantClass.capFundamental_comp :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom] (d : ℕ)
    [RelativeDimension X.hom d] (p q : ℤ)
    (c : group (fun _ ↦ 0) (𝟙 X) p) (c' : group (fun _ ↦ 0) (𝟙 X) q),
    capFundamental (fun _ ↦ 0) X (d : ℤ) (p + q)
        (identityComp (fun _ ↦ 0) X c c') =
      RelativeChow.castDegree (fun _ ↦ 0) (capFundamental_comp_degree d p q)
        (ChowGroup.smoothIntersectionProduct X d
          (capFundamental (fun _ ↦ 0) X (d : ℤ) p c)
          (capFundamental (fun _ ↦ 0) X (d : ℤ) q c')))
