/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.AtPoint
import StacksCheckRecall

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X) (V : S.affineOpens)
  (hsV : f x ∈ (V : S.Opens))

/- Lemma 29.30.10: syntomicity at a point is equivalent both to admitting a
standard syntomic affine neighborhood over any prescribed affine neighborhood
of the image and to the finite-presentation, flat-stalk, and complete-intersection
closed-fiber criterion. -/
@[stacks 01UE] #check
  (AlgebraicGeometry.Scheme.Hom.syntomicAt_tfae (f := f) x V hsV :
    List.TFAE [
      SyntomicAt f x,
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : U ≤ f ⁻¹ᵁ V,
          StandardSyntomic (f.resLE V U e),
      FinitePresentationAt f x ∧
        ((f.stalkMap x).hom.Flat ∧ f.closedFiberCompleteIntersectionAt x)])

/- The fixed-target affine-neighborhood criterion. -/
#check
  (AlgebraicGeometry.Scheme.Hom.syntomicAt_iff_exists_standardSyntomic_affineChart_over
      (f := f) x V hsV :
    SyntomicAt f x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : U ≤ f ⁻¹ᵁ V,
          StandardSyntomic (f.resLE V U e))

/- The intrinsic stalk-and-fiber criterion. -/
#check
  (AlgebraicGeometry.Scheme.Hom.syntomicAt_iff_localCriterion
      (f := f) x :
    SyntomicAt f x ↔
      FinitePresentationAt f x ∧
        ((f.stalkMap x).hom.Flat ∧ f.closedFiberCompleteIntersectionAt x))

end AlgebraicGeometry.Scheme.Hom
