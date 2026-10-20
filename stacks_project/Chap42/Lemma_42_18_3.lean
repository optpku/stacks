module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Principal.Pushforward.ProperCurve
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicCycle

/- Lemma 42.18.3: on a one-dimensional integral scheme proper over a field, the
pushforward of a principal cycle to the base spectrum is zero. -/
@[stacks 02RU] #check (AlgebraicGeometry.AlgebraicCycle.map_principal_toSpec_eq_zero :
  ∀ {K : Type u} [Field K] (X : SchemeOverField K) [IsIntegral X.left]
    [IsProper X.hom] (hdim : topologicalKrullDim X.left = 1)
    (f : X.left.functionFieldˣ),
    -- Local instance justification (proof-local temporary data): properness supplies it only to elaborate `principal` in this typed check.
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    map X.hom
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (fun _ : Spec (CommRingCat.of K) ↦ 0)
        (principal X.left f) = 0)

/- The coefficient over the base point is the residue-degree-weighted sum of orders. -/
#check (AlgebraicGeometry.AlgebraicCycle.map_principal_toSpec_apply :
  ∀ {K : Type u} [Field K] (X : SchemeOverField K) [IsIntegral X.left]
    [IsProper X.hom] (hdim : topologicalKrullDim X.left = 1)
    (f : X.left.functionFieldˣ),
    -- Local instance justification (proof-local temporary data): properness supplies it only to elaborate `principal` and `ord` in this typed check.
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    map X.hom
        (X.hom.relativeDimensionFunction (fun _ : Spec (CommRingCat.of K) ↦ 0))
        (fun _ : Spec (CommRingCat.of K) ↦ 0)
        (principal X.left f) default =
      ∑ᶠ x : closedPoints X.left,
        (Module.finrank K (X.left.residueField x.1) : ℤ) * X.left.ord f x.1)

end AlgebraicGeometry.AlgebraicCycle

namespace AlgebraicGeometry.SchemeOverField

/- The displayed residue-degree-weighted sum of orders vanishes. -/
#check (AlgebraicGeometry.SchemeOverField.finsum_residueDegree_mul_ord_eq_zero :
  ∀ {K : Type u} [Field K] (X : SchemeOverField K) [IsIntegral X.left]
    [IsProper X.hom] (hdim : topologicalKrullDim X.left = 1)
    (f : X.left.functionFieldˣ),
    -- Local instance justification (proof-local temporary data): properness supplies it only to elaborate `ord` in this typed check.
    letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
    ∑ᶠ x : closedPoints X.left,
      (Module.finrank K (X.left.residueField x.1) : ℤ) * X.left.ord f x.1 = 0)

end AlgebraicGeometry.SchemeOverField
