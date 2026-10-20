module

public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import ReasLib.AlgebraicGeometry.ChowGroup.MilnorComplex

/-!
# First higher Chow groups

This file defines the first higher Chow group as the homology in the middle of the primed
Milnor complex, together with its identification with `ShortComplex.homology` and the
identification of the cokernel of the second boundary with the ordinary Chow group.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Pointwise

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable (d : X → ℤ) [IsDimensionFunction d] (k : ℤ)

/-- The first higher Chow group `CH^M_k(X, 1)` is the homology of the primed Milnor complex
at the degree-one term, realized as the quotient of `ker(secondBoundary)` by the image of
the tame-symbol boundary. -/
abbrev firstHigher : Type u :=
  AddMonoidHom.ker (milnorComplex d k).g.hom ⧸
    AddMonoidHom.range (milnorComplex d k).abToCycles

/-- The first higher Chow group is canonically isomorphic to the homology of the primed
Milnor short complex. -/
def firstHigherIso :
    AddCommGrpCat.of (firstHigher d k) ≅ (milnorComplex d k).homology :=
  (milnorComplex d k).abHomologyIso.symm

/-- The canonical quotient map from primed degree-one cycles onto the first higher Chow group. -/
abbrev firstHigher_mk :
    AddMonoidHom.ker (milnorComplex d k).g.hom →+ firstHigher d k :=
  QuotientAddGroup.mk' (AddMonoidHom.range (milnorComplex d k).abToCycles)

/-- The cokernel of the second primed Milnor boundary is canonically the ordinary Chow group,
via the identification of primed `K₀ᴹ` with cycles and of the image of `∂` with rational
equivalence. -/
def homologyZeroIso :
    (CycleGroup.Pointwise.locallyFinite d k ⧸ AddMonoidHom.range (secondBoundary d k)) ≃+
      ChowGroup X d k :=
  QuotientAddGroup.congr (AddMonoidHom.range (secondBoundary d k))
    (RationalEquivalence.boundaries d k) (CycleGroup.Pointwise.equiv d k).symm sorry

/-- The zero homology of the primed Milnor complex is identified with the Chow group of
degree-`k` cycles. -/
theorem homologyZeroIso_apply
    (n : CycleGroup.Pointwise.locallyFinite d k) :
    homologyZeroIso d k (QuotientAddGroup.mk n) =
      chowClass d k ((CycleGroup.Pointwise.equiv d k).symm n) := sorry

end AlgebraicGeometry.ChowGroup.Pointwise

namespace AlgebraicGeometry.ChowGroup

/-- The first Milnor higher Chow group of a scheme locally of finite type over a universally
catenary base, graded by the induced relative dimension function. -/
abbrev firstHigher {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) : Type u :=
  @Pointwise.firstHigher X (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance k

/-- The relative first higher Chow group is canonically the homology of its locally finite
Milnor complex. -/
def firstHigherIso {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
    [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ] (k : ℤ) :
    AddCommGrpCat.of (firstHigher p δ k) ≅ (milnorComplex p δ k).homology :=
  @Pointwise.firstHigherIso X (LocallyOfFiniteType.isLocallyNoetherian p)
    (p.relativeDimensionFunction δ) inferInstance k

end AlgebraicGeometry.ChowGroup
