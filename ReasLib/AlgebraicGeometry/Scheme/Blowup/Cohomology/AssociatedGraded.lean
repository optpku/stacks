/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.SectionMaps
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Module.Associated.TwistedSections
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.Algebra.Module.Graded.Shift.NatInt
public import ReasLib.RingTheory.Ideal.AssociatedGraded.Basic

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.IsBlowup

/-- The projective spectrum of the associated graded ring `Gr_I(A)`. -/
noncomputable abbrev associatedGradedProj
    {A : Type u} [CommRing A] (I : Ideal A) : Scheme.{u} :=
  AlgebraicGeometry.Proj
    (A := Ideal.AssociatedGraded.ring I)
    (σ := Submodule A (Ideal.AssociatedGraded.ring I))
    (Ideal.AssociatedGraded.grade I)

/-- The canonical morphism from `Proj(Gr_I(A))` to the spectrum of its degree-zero ring. -/
noncomputable abbrev associatedGradedProjToSpec
    {A : Type u} [CommRing A] (I : Ideal A) :
    associatedGradedProj I ⟶
      Spec (CommRingCat.of (Ideal.AssociatedGraded.grade I 0)) :=
  AlgebraicGeometry.Proj.toSpecZero
    (A := Ideal.AssociatedGraded.ring I)
    (σ := Submodule A (Ideal.AssociatedGraded.ring I))
    (Ideal.AssociatedGraded.grade I)

/-- The maximum fibre-dimension bound of `Proj(Gr_I(A))` over its degree-zero base. -/
noncomputable def associatedGradedFiberDimension
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) : ℕ :=
  sInf {d : ℕ |
    ∀ x : associatedGradedProj I,
      (associatedGradedProjToSpec I).fiberDimensionAt x ≤
        (d : WithBot ℕ∞)}

/-- The associated-graded fibre-dimension invariant bounds every fibre of
`Proj(Gr_I(A))` over its degree-zero base. -/
theorem associatedGradedFiberDimension_bound
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    ∀ x : associatedGradedProj I,
      (associatedGradedProjToSpec I).fiberDimensionAt x ≤
        (associatedGradedFiberDimension I : WithBot ℕ∞) := sorry

/-- The associated-graded fibre dimension is the least natural-number bound
for all fibres of `Proj(Gr_I(A))` over its degree-zero base. -/
theorem associatedGradedFiberDimension_minimal
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (d : ℕ)
    (hd : ∀ x : associatedGradedProj I,
      (associatedGradedProjToSpec I).fiberDimensionAt x ≤
        (d : WithBot ℕ∞)) :
    associatedGradedFiberDimension I ≤ d := sorry

/-- The associated-graded fibre-dimension invariant is zero when
`Proj(Gr_I(A))` is empty. -/
theorem associatedGradedFiberDimension_eq_zero_of_isEmpty
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    [IsEmpty (associatedGradedProj I)] :
    associatedGradedFiberDimension I = 0 := sorry

/-- For a blowup of `Spec A` along `I`, the associated-graded invariant bounds
the dimension of every blowup fibre at a point of the source. -/
theorem associatedGradedFiberDimension_blowup_bound
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] (x : X) :
    p.fiberDimensionAt x ≤ (associatedGradedFiberDimension I : WithBot ℕ∞) := sorry

/-- Positive cohomology of all canonical associated-graded twists vanishes above `q`. -/
def associatedGradedPositiveVanishingAt
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (q : ℕ) : Prop :=
  ∀ i : ℕ, 0 < i → ∀ m : ℕ, q ≤ m →
    IsZero
      (Scheme.Hom.cohomology
        (associatedGradedProjToSpec I)
        (ProjTwistFamily.tensorTwist
          (Proj.AssociatedModule.twistingSheaf
            (R := A) (A := Ideal.AssociatedGraded.ring I)
            (Ideal.AssociatedGraded.grade I))
          (SheafOfModules.unit
            (associatedGradedProj I).ringCatSheaf)
          (m : ℤ)) i)

/-- The degree-zero associated graded piece maps isomorphically to global sections in every
degree at least `q`. -/
def associatedGradedDegreeZeroAt
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (q : ℕ) : Prop :=
  ∀ m : ℕ, q ≤ m →
    IsIso
      (Proj.AssociatedModule.degreeZeroToGlobalSectionsHom
        (R := A) (A := Ideal.AssociatedGraded.ring I)
        (Ideal.AssociatedGraded.grade I)
        (GradedModule.shiftGrading
          (DirectSum.Decomposition.natToIntGrading
            (Ideal.AssociatedGraded.grade I)) (m : ℤ)))

/-- The least threshold where both positive vanishing and the degree-zero associated-section
identification hold. -/
noncomputable def associatedGradedUniformityThreshold
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) : ℕ :=
  sInf {q : ℕ |
    associatedGradedPositiveVanishingAt I q ∧ associatedGradedDegreeZeroAt I q}

/-- The threshold specification exposes both defining conditions of `q(S)`. -/
theorem associatedGradedUniformityThreshold_spec
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) :
    associatedGradedPositiveVanishingAt I (associatedGradedUniformityThreshold I) ∧
      associatedGradedDegreeZeroAt I (associatedGradedUniformityThreshold I) := sorry

/-- Every threshold satisfying both associated-graded uniformity conditions is at least the
canonical least threshold. -/
theorem associatedGradedUniformityThreshold_minimal
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) (q : ℕ)
    (hq : associatedGradedPositiveVanishingAt I q ∧ associatedGradedDegreeZeroAt I q) :
    associatedGradedUniformityThreshold I ≤ q := sorry

end AlgebraicGeometry.IsBlowup
