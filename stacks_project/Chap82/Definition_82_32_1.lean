/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChowGroup.Degree
import StacksCheckRecall

/-!
# Degree of zero-cycle classes on proper algebraic spaces over a field
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Definition 82.32.1: Let k be a field. Let p : X ⟶ Spec k be a proper morphism
of algebraic spaces. The degree of a zero-cycle class on X is the composite
p_* : CH_0(X) ⟶ CH_0(Spec k) ⟶ ℤ of proper pushforward on Chow groups
(Lemma 82.16.3) with the natural isomorphism CH_0(Spec k) ≃ ℤ sending
[Spec k] to 1. Notation: deg(α). -/
@[stacks 0ESG]
#check (AlgebraicGeometry.AlgebraicSpace.Hom.chowDegree :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (SchemeRealization.toBase X)],
    Hom.chowGroup (SchemeRealization.toBase X) (fun _ ↦ (0 : ℤ)) 0 →+ ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.specFieldChowEquiv :
  ∀ (k : Type u) [Field k],
    Hom.chowGroup
      (SchemeRealization.toBase (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of k))))))
      (fun _ ↦ (0 : ℤ)) 0 ≃+ ℤ)

#check (AlgebraicGeometry.AlgebraicSpace.Hom.specFieldChowEquiv_fundamentalClass :
  ∀ (k : Type u) [Field k],
    Hom.specFieldChowEquiv k (Hom.specFieldFundamentalClass k) = 1)

end AlgebraicGeometry.AlgebraicSpace
