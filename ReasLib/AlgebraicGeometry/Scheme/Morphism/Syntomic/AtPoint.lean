/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Syntomic.Standard

/-!
# Syntomic morphisms at a point

This module gives affine-neighborhood and intrinsic local criteria for a
scheme morphism to be syntomic at a point.
-/

@[expose] public section

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Given an affine neighborhood `V` of `f x`, a morphism is syntomic at `x`
exactly when some affine neighborhood of `x` restricts to a standard syntomic
morphism over `V`. -/
theorem syntomicAt_iff_exists_standardSyntomic_affineChart_over
    (x : X) (V : S.affineOpens) (hsV : f x ∈ (V : S.Opens)) :
    SyntomicAt f x ↔
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : U ≤ f ⁻¹ᵁ V,
          StandardSyntomic (f.resLE V U e) := sorry

/-- A morphism is syntomic at a point exactly when it is finitely presented
there, its stalk map is flat, and its closed fiber is a complete intersection
over the residue field of the image point. -/
theorem syntomicAt_iff_localCriterion
    (x : X) :
    SyntomicAt f x ↔
      FinitePresentationAt f x ∧
        ((f.stalkMap x).hom.Flat ∧ f.closedFiberCompleteIntersectionAt x) := sorry

/-- For an affine neighborhood `V` of `f x`, syntomicity at `x`, the existence
of a standard syntomic affine chart over `V`, and the intrinsic stalk-and-fiber
criterion are equivalent. -/
theorem syntomicAt_tfae
    (x : X) (V : S.affineOpens) (hsV : f x ∈ (V : S.Opens)) :
    List.TFAE [
      SyntomicAt f x,
      ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ e : U ≤ f ⁻¹ᵁ V,
          StandardSyntomic (f.resLE V U e),
      FinitePresentationAt f x ∧
        ((f.stalkMap x).hom.Flat ∧ f.closedFiberCompleteIntersectionAt x)] := sorry

end AlgebraicGeometry.Scheme.Hom
