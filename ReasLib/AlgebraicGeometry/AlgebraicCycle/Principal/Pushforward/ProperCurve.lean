/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal.Pushforward
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/-- The pushforward to the base field of a principal cycle on a proper integral curve is zero. -/
theorem map_principal_toSpec_eq_zero
    {K : Type u} [Field K] (X : SchemeOverField K) [IsIntegral X.left]
    [IsProper X.hom] (hdim : topologicalKrullDim X.left = 1)
    (f : X.left.functionFieldˣ) :
    -- Local instance justification (proof-local temporary data): properness supplies it only to elaborate `principal` in this proposition.
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    map X.hom
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (fun _ : Spec (CommRingCat.of K) ↦ 0)
        (principal X.left f) = 0 := sorry

/-- The coefficient over the base point of the pushforward of a principal cycle is the
residue-degree-weighted sum of its orders at closed points. -/
theorem map_principal_toSpec_apply
    {K : Type u} [Field K] (X : SchemeOverField K) [IsIntegral X.left]
    [IsProper X.hom] (hdim : topologicalKrullDim X.left = 1)
    (f : X.left.functionFieldˣ) :
    -- Local instance justification (proof-local temporary data): properness supplies it only to elaborate `principal` and `ord` in this proposition.
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    map X.hom
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (fun _ : Spec (CommRingCat.of K) ↦ 0)
        (principal X.left f) default =
      ∑ᶠ x : closedPoints X.left,
        (Module.finrank K (X.left.residueField x.1) : ℤ) * X.left.ord f x.1 := sorry

end AlgebraicGeometry.AlgebraicCycle

namespace AlgebraicGeometry.SchemeOverField

/-- The residue-degree-weighted sum of the orders of a function-field unit on a proper integral
curve over a field is zero. -/
theorem finsum_residueDegree_mul_ord_eq_zero
    {K : Type u} [Field K] (X : SchemeOverField K) [IsIntegral X.left]
    [IsProper X.hom] (hdim : topologicalKrullDim X.left = 1)
    (f : X.left.functionFieldˣ) :
    -- Local instance justification (proof-local temporary data): properness supplies it only to elaborate `ord` in this proposition.
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    ∑ᶠ x : closedPoints X.left,
      (Module.finrank K (X.left.residueField x.1) : ℤ) * X.left.ord f x.1 = 0 := sorry

end AlgebraicGeometry.SchemeOverField
