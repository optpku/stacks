/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.IntersectionCycle

@[expose] public section

open AlgebraicGeometry CategoryTheory Function Set Topology

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

/-- The support of the restricted ambient intersection cycle lies in its open domain. -/
theorem intersectionCycleOnOpen_supportWithinDomain [IsLocallyNoetherian Y]
    (C : Y.IdealSheafData) (i : X ⟶ Y) [h_i : IsClosedImmersion i]
    (U : X.Opens) (hproper : TopologicalSpace.Closeds.IntersectProperly C.support i.ker.support) :
    (fun x : U.toScheme ↦
      C.intersectionCycle i.ker hproper ((U.ι ≫ i) x)).support ⊆ Set.univ := sorry

/-- The support of the restricted ambient intersection cycle is locally finite in its open
domain. -/
theorem intersectionCycleOnOpen_supportLocallyFiniteWithinDomain [IsLocallyNoetherian Y]
    (C : Y.IdealSheafData) (i : X ⟶ Y) [h_i : IsClosedImmersion i]
    (U : X.Opens) (hproper : TopologicalSpace.Closeds.IntersectProperly C.support i.ker.support) :
    ∀ x ∈ (Set.univ : Set U.toScheme), ∃ t ∈ 𝓝 x,
      Set.Finite (t ∩ (fun y : U.toScheme ↦
        C.intersectionCycle i.ker hproper ((U.ι ≫ i) y)).support) := sorry

/-- The restriction to an open of a closed subscheme of the ambient intersection cycle. -/
noncomputable def intersectionCycleOnOpen [IsLocallyNoetherian Y]
    (C : Y.IdealSheafData) (i : X ⟶ Y) [h_i : IsClosedImmersion i]
    (U : X.Opens) (hproper : TopologicalSpace.Closeds.IntersectProperly C.support i.ker.support) :
    AlgebraicCycle U.toScheme ℤ where
  toFun := fun x ↦ C.intersectionCycle i.ker hproper ((U.ι ≫ i) x)
  supportWithinDomain' := intersectionCycleOnOpen_supportWithinDomain C i U hproper
  supportLocallyFiniteWithinDomain' :=
    intersectionCycleOnOpen_supportLocallyFiniteWithinDomain C i U hproper

/-- The coefficient of the restricted intersection cycle is its ambient coefficient at the
image point. -/
theorem intersectionCycleOnOpen_apply [IsLocallyNoetherian Y]
    (C : Y.IdealSheafData) (i : X ⟶ Y) [h_i : IsClosedImmersion i]
    (U : X.Opens) (hproper : TopologicalSpace.Closeds.IntersectProperly C.support i.ker.support) (x : U.toScheme) :
    C.intersectionCycleOnOpen i U hproper x =
      C.intersectionCycle i.ker hproper ((U.ι ≫ i) x) := sorry

end AlgebraicGeometry.Scheme.IdealSheafData
