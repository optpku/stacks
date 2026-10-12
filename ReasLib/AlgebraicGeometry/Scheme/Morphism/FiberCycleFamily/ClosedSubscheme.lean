/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Mathlib.Topology.KrullDimension
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily

/-!
# Associated cycle families of closed subschemes

This file associates to a closed subscheme of bounded fibre dimension the family
of `r`-cycles on the scheme-theoretic fibres given by the associated cycle of
each fibre.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}}

/-- The inverse image of a closed subscheme in the scheme-theoretic fibre over `s`. -/
noncomputable def fiberClosedSubscheme (f : X ⟶ S) (Z : X.IdealSheafData) (s : S) :
    (f.fiber s).IdealSheafData :=
  Z.comap (f.fiberι s)

/-- The inverse image of `Z` in `X_s` is the pullback of the ideal sheaf along the fibre
inclusion. -/
theorem fiberClosedSubscheme_def (f : X ⟶ S) (Z : X.IdealSheafData) (s : S) :
    f.fiberClosedSubscheme Z s = Z.comap (f.fiberι s) := sorry

/-- The inverse image of `Z` in `X_s` is isomorphic to the scheme-theoretic fibre of
`Z ⟶ S` at `s`. -/
noncomputable def fiberClosedSubschemeIso (f : X ⟶ S) (Z : X.IdealSheafData) (s : S) :
    (f.fiberClosedSubscheme Z s).subscheme ≅ (Z.subschemeι ≫ f).fiber s :=
  Z.comapIso (f.fiberι s) ≪≫
    pullbackSymmetry (f.fiberι s) Z.subschemeι ≪≫
    pullbackRightPullbackFstIso f (S.fromSpecResidueField s) Z.subschemeι

/-- The comparison isomorphism, the fibre inclusion of `Z ⟶ S`, and the closed
immersion of `Z` recover the composite of the closed immersion of `Z_s` in `X_s`
with the fibre inclusion of `X_s`. -/
theorem fiberClosedSubschemeIso_hom_fiberι (f : X ⟶ S) (Z : X.IdealSheafData) (s : S) :
    (f.fiberClosedSubschemeIso Z s).hom ≫
        (Z.subschemeι ≫ f).fiberι s ≫ Z.subschemeι =
      (f.fiberClosedSubscheme Z s).subschemeι ≫ f.fiberι s := sorry

/-- The fibrewise bound `dim(Z_s) ≤ r` on a closed subscheme. -/
def fiberClosedSubschemeDimensionLE (f : X ⟶ S) (Z : X.IdealSheafData) (r : ℕ) : Prop :=
  ∀ s : S, topologicalKrullDim (f.fiberClosedSubscheme Z s).subscheme ≤ (r : WithBot ℕ∞)

/-- The topological Krull-dimension bound on `Z_s` is equivalent to a bound on the
`δ`-dimension of `Z_s` computed with the constant-zero dimension function on `Spec κ(s)`. -/
theorem fiberClosedSubschemeDimensionLE_iff (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ) :
    f.fiberClosedSubschemeDimensionLE Z r ↔
      ∀ s : S,
        (f.fiberToSpecResidueField s).closedSubschemeDeltaDimension (fun _ ↦ (0 : ℤ))
          (f.fiberClosedSubscheme Z s) ≤ (r : EInt) := sorry

/-- Convert a topological Krull-dimension bound on `Z_s` into the `δ`-dimension bound
required by the associated-cycle construction. -/
theorem fiberClosedSubschemeDeltaDimension_le_of_topologicalKrullDim_le
    (f : X ⟶ S) [LocallyOfFiniteType f] (Z : X.IdealSheafData) (r : ℕ) {s : S}
    (h : topologicalKrullDim (f.fiberClosedSubscheme Z s).subscheme ≤ (r : WithBot ℕ∞)) :
    (f.fiberToSpecResidueField s).closedSubschemeDeltaDimension (fun _ ↦ (0 : ℤ))
      (f.fiberClosedSubscheme Z s) ≤ (r : EInt) := sorry

/-- The family of `r`-cycles on fibres of `X/S` associated to a closed subscheme of
fibre dimension at most `r`. -/
noncomputable def closedSubschemeFiberCycleFamily (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r) :
    f.FiberCycleFamily (r : ℤ) :=
  fun s ↦ (f.fiberToSpecResidueField s).closedSubschemeCycle (fun _ ↦ (0 : ℤ))
    (f.fiberClosedSubscheme Z s) (r : ℤ)
    (fiberClosedSubschemeDeltaDimension_le_of_topologicalKrullDim_le f Z r (hZ s))

/-- Evaluating the associated fibrewise cycle family recovers the associated cycle of the
fibre closed subscheme. -/
theorem closedSubschemeFiberCycleFamily_apply (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r) (s : S) :
    closedSubschemeFiberCycleFamily f Z r hZ s =
      (f.fiberToSpecResidueField s).closedSubschemeCycle (fun _ ↦ (0 : ℤ))
        (f.fiberClosedSubscheme Z s) (r : ℤ)
        (fiberClosedSubschemeDeltaDimension_le_of_topologicalKrullDim_le f Z r (hZ s)) :=
  sorry

/-- The associated fibrewise cycle family is `([Z_s]_r)_{s ∈ S}`, where `Z_s` is the
inverse image of `Z` in the fibre `X_s`. -/
theorem closedSubschemeFiberCycleFamily_spec (f : X ⟶ S) [LocallyOfFiniteType f]
    (Z : X.IdealSheafData) (r : ℕ) (hZ : f.fiberClosedSubschemeDimensionLE Z r) (s : S) :
    closedSubschemeFiberCycleFamily f Z r hZ s =
        (f.fiberToSpecResidueField s).closedSubschemeCycle (fun _ ↦ (0 : ℤ))
          (Z.comap (f.fiberι s)) (r : ℤ)
          (fiberClosedSubschemeDeltaDimension_le_of_topologicalKrullDim_le f Z r (hZ s)) ∧
      f.fiberClosedSubscheme Z s = Z.comap (f.fiberι s) := sorry

end AlgebraicGeometry.Scheme.Hom
