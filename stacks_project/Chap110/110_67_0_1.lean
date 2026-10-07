module

import StacksCheckRecall

public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.Fiber
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.PointRestriction

/-!
# A displayed Picard non-membership criterion on the origin fibre
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The origin of the affine line `𝔸(PUnit; Spec k)`, obtained by evaluating the
zero section on the unique point of `Spec k`. -/
def affineLineOrigin (k : Type u) [Field k] :
    𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k)) :=
  AffineSpace.homOfVector (𝟙 (Spec (CommRingCat.of k))) (fun _ ↦ 0)
    (IsLocalRing.closedPoint k)

variable {k : Type u} [Field k] {Y : Scheme.{u}}
  (f : Y ⟶ 𝔸(PUnit.{u + 1}; Spec (CommRingCat.of k)))
  (y : f.fiber (affineLineOrigin k))
  (hy : y ∈ closedPoints (f.fiber (affineLineOrigin k)))
  [IsEffectiveCartierDivisor
    (IdealSheafData.vanishingIdeal
      ⟨({y} : Set (f.fiber (affineLineOrigin k))), hy⟩).subschemeι]

/- 110.67.0.1: the condition imposed on the chosen rational point in the proper
flat cubic-family construction is that `𝒪(n y)` on the origin fibre lies outside
the image of Picard restriction for every positive natural number `n`. This
specifies the condition, not a theorem asserting it for every point. -/
@[stacks 0DYB] #check
  (AlgebraicGeometry.Scheme.Hom.HasNonextendablePointMultiples
    (f.fiberι (affineLineOrigin k)) y hy : Prop)

#check (AlgebraicGeometry.Scheme.Hom.hasNonextendablePointMultiples_iff
  (f.fiberι (affineLineOrigin k)) y hy :
  Hom.HasNonextendablePointMultiples (f.fiberι (affineLineOrigin k)) y hy ↔
    ∀ n : ℕ, 0 < n →
      n • closedPointPicardClass y hy ∉
        AddMonoidHom.range (Hom.picardPullback (f.fiberι (affineLineOrigin k))))

end AlgebraicGeometry.Scheme
