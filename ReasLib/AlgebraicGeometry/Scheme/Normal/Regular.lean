module

public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Normal
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Normal
public import ReasLib.AlgebraicGeometry.Scheme.Dimension.Stalk
public import ReasLib.RingTheory.Normal.RegularLocal

/-!
# Normal and regular schemes

This file relates regularity and normality for schemes through their local rings, including the
regularity of locally Noetherian normal schemes of dimension at most one.
-/

@[expose] public section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- If the stalk of a scheme at a point is a regular local ring, then the scheme is normal at
that point. -/
theorem isNormalAt_of_isRegularLocalRing_stalk (x : X)
    (hx : IsRegularLocalRing (X.presheaf.stalk x)) :
    X.isNormalAt x := by
  exact @IsRegularLocalRing.isNormalRing _ _ hx

/-- Every regular scheme is normal at each of its points. -/
theorem Regular.isNormalAt (hX : Regular X) (x : X) :
    X.isNormalAt x := by
  exact isNormalAt_of_isRegularLocalRing_stalk x (@isRegularLocalRing_stalk X hX x)

/-- Every regular scheme is normal. -/
theorem Regular.isNormal (hX : Regular X) :
    X.isNormal := fun x ↦ hX.isNormalAt x

/-- A scheme whose stalk at every point is a regular local ring is normal. -/
theorem isNormal_of_isRegularLocalRing_stalk
    (hX : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x)) :
    X.isNormal := fun x ↦
  isNormalAt_of_isRegularLocalRing_stalk x (hX x)

/-- A locally Noetherian normal scheme of topological Krull dimension at most one is regular. -/
theorem regular_of_isNormal_of_topologicalKrullDim_le_one (X : Scheme.{u})
    [IsLocallyNoetherian X] (hnormal : X.isNormal) (hdim : topologicalKrullDim X ≤ 1) :
    Regular X := by
  refine (regular_iff_isLocallyNoetherian_and_forall_isRegularLocalRing_stalk X).2 ⟨inferInstance, ?_⟩
  have hR1 : satisfiesSerreConditionR X 1 := ((isNormal_iff_serre X).1 hnormal).2
  rw [topologicalKrullDim_eq_iSup_ringKrullDim_stalk X] at hdim
  intro x
  exact hR1.isRegularLocalRing_stalk x
    ((le_iSup (fun y ↦ ringKrullDim (X.presheaf.stalk y)) x).trans hdim)

end AlgebraicGeometry.Scheme

end
