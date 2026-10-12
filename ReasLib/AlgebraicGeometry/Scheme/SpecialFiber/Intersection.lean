/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.SpecialFiber

/-- The reduced irreducible component of the closed fibre indexed by `i`. -/
noncomputable abbrev component
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) : Scheme.{u} :=
  (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubscheme i

/-- The morphism from a reduced closed-fibre component to the total space. -/
noncomputable abbrev componentInclusion
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    component f i ⟶ X :=
  (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubschemeι i ≫
    f.fiberι (IsLocalRing.closedPoint R)

/-- The morphism from a reduced closed-fibre component to the residue-field spectrum. -/
noncomputable abbrev componentToResidueField
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    component f i ⟶ Spec ((Spec (CommRingCat.of R)).residueField
      (IsLocalRing.closedPoint R)) :=
  (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubschemeι i ≫
    f.fiberToSpecResidueField (IsLocalRing.closedPoint R)

/-- A reduced component of a proper model is proper over the closed-point residue field. -/
instance instIsProperComponentToResidueField
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    IsProper (componentToResidueField f i) := sorry

/-- A component of the special fibre of a regular model has dimension at most one. -/
theorem component_dimension_le_one
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (i : Fin n) :
    topologicalKrullDim (component f (components i)) ≤ 1 := sorry

/-- The degree of an invertible module on a reduced closed-fibre component. -/
noncomputable def componentDegree
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper : IsProper (componentToResidueField f i))
    (h_component_dimension : topologicalKrullDim (component f i) ≤ 1)
    (L : (component f i).Modules) [Scheme.Modules.Invertible L] : ℤ :=
  @Scheme.Modules.curveDegreeOfInvertible _ _ _ _ h_component_proper
    h_component_dimension L inferInstance

/-- The Picard class of an integral component divisor with coefficient vector `b`. -/
noncomputable def divisorClass
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (b : Fin n → ℤ) : X.PicardGroup :=
  Fintype.linearCombination ℤ (fun i ↦
    Scheme.Modules.picardClass (f.specialFiberComponent (components i)).associatedSheaf) b

/-- A basis coefficient maps to the positive associated sheaf of its component. -/
theorem divisorClass_single
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (i : Fin n) :
    divisorClass f n components (Pi.single i 1) =
      Scheme.Modules.picardClass (f.specialFiberComponent (components i)).associatedSheaf := sorry

/-- The component-degree pairing of a coefficient vector with a Picard class. -/
noncomputable def degreePairing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)))
    (h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1)
    (a : Fin n → ℤ) (x : X.PicardGroup) : ℤ :=
  ∑ i, a i * componentDegree f (components i) (h_component_proper i)
    (h_component_dimension i)
    ((Scheme.Modules.pullback (componentInclusion f (components i))).obj
      (Scheme.PicardGroup.repr x))

/-- Evaluation of the pairing on an explicit invertible module representative. -/
theorem degreePairing_picardClass
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)))
    (h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1)
    (a : Fin n → ℤ) (L : X.Modules) [Scheme.Modules.Invertible L] :
    degreePairing f n components h_component_proper h_component_dimension a
        (Scheme.Modules.picardClass L) =
      ∑ i, a i * componentDegree f (components i) (h_component_proper i)
        (h_component_dimension i)
        ((Scheme.Modules.pullback (componentInclusion f (components i))).obj L) := sorry

/-- The integral bilinear form whose matrix entries are component degrees. -/
noncomputable def intersectionForm
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)))
    (h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1) :
    LinearMap.BilinForm ℤ (Fin n → ℤ) :=
  Matrix.toBilin' (fun i j ↦
    componentDegree f (components i) (h_component_proper i) (h_component_dimension i)
      ((Scheme.Modules.pullback (componentInclusion f (components i))).obj
        (f.specialFiberComponent (components j)).associatedSheaf))

/-- Evaluation of the intersection form is the degree pairing with the associated divisor class. -/
theorem intersectionForm_apply
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)))
    (h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1)
    (a b : Fin n → ℤ) :
    intersectionForm f n components h_component_proper h_component_dimension a b =
      degreePairing f n components h_component_proper h_component_dimension a
        (divisorClass f n components b) := sorry

/-- The geometric intersection form is symmetric on the component lattice. -/
theorem intersectionForm_isSymm
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [Scheme.Regular X]
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)))
    (h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1) :
    (intersectionForm f n components h_component_proper h_component_dimension).IsSymm := sorry

/-- The intersection of two component divisors equals either associated degree pairing. -/
theorem intersectionForm_eq_degreePairings
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (a b : Fin n → ℤ) :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    intersectionForm f n components h_component_proper h_component_dimension a b =
        degreePairing f n components h_component_proper h_component_dimension a
          (divisorClass f n components b) ∧
      degreePairing f n components h_component_proper h_component_dimension a
          (divisorClass f n components b) =
        degreePairing f n components h_component_proper h_component_dimension b
          (divisorClass f n components a) := sorry

end AlgebraicGeometry.Scheme.Hom.SpecialFiber
