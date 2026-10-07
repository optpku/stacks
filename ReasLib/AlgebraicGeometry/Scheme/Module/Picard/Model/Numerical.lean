module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import ReasLib.AlgebraicGeometry.NumericalType.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Model.ExactSequence
public import ReasLib.AlgebraicGeometry.Scheme.OverField.GlobalSections.Degree
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.IntersectionPairing
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Weight

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.SpecialFiber

/-- The component degree is divisible by the residue-field degree of its component. -/
theorem componentWeight_dvd_degree
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
    (i : Fin n) (L : (component f (components i)).Modules)
    [Scheme.Modules.Invertible L] :
    (componentWeight f (components i) : ℤ) ∣
      componentDegree f (components i)
        (instIsProperComponentToResidueField f (components i))
        (component_dimension_le_one C h_globalSections f genericFiberIso n components i) L := sorry

/-- The normalized degree of a model Picard class on each indexed component. -/
noncomputable def normalizedDegree
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
    (x : X.PicardGroup) (i : Fin n) : ℤ :=
  let h_component_proper : ∀ j, IsProper (componentToResidueField f (components j)) :=
    fun j ↦ instIsProperComponentToResidueField f (components j)
  let h_component_dimension : ∀ j, topologicalKrullDim (component f (components j)) ≤ 1 :=
    fun j ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components j
  degreePairing f n components h_component_proper h_component_dimension (Pi.single i 1) x /
    (componentWeight f (components i) : ℤ)

/-- The normalized degree at the zero Picard class is zero. -/
theorem normalizedDegree_zero
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    normalizedDegree C h_globalSections f genericFiberIso n components 0 = 0 := sorry

/-- The normalized degree is additive on model Picard classes. -/
theorem normalizedDegree_add
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
    (x y : X.PicardGroup) :
    normalizedDegree C h_globalSections f genericFiberIso n components (x + y) =
      normalizedDegree C h_globalSections f genericFiberIso n components x +
        normalizedDegree C h_globalSections f genericFiberIso n components y := sorry

/-- The additive homomorphism of normalized component degrees. -/
noncomputable def normalizedDegreeMap
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    X.PicardGroup →+ (Fin n → ℤ) :=
  { toFun := normalizedDegree C h_globalSections f genericFiberIso n components
    map_zero' := normalizedDegree_zero C h_globalSections f genericFiberIso n components
    map_add' := normalizedDegree_add C h_globalSections f genericFiberIso n components }

/-- The normalized-degree map evaluates on an invertible module by component degree divided by weight. -/
theorem normalizedDegreeMap_picardClass
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
    (L : X.Modules) [Scheme.Modules.Invertible L] :
    normalizedDegreeMap C h_globalSections f genericFiberIso n components
        (Scheme.Modules.picardClass L) =
      fun i ↦ componentDegree f (components i)
        (instIsProperComponentToResidueField f (components i))
        (component_dimension_le_one C h_globalSections f genericFiberIso n components i)
        ((Scheme.Modules.pullback (componentInclusion f (components i))).obj L) /
        (componentWeight f (components i) : ℤ) := sorry

end AlgebraicGeometry.Scheme.Hom.SpecialFiber

namespace NumericalType

/-- A numerical type is associated to a regular model when all its coordinates are geometric. -/
public def IsAssociatedTo
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) : Prop :=
  (∀ i, T.multiplicity i = f.specialFiberMultiplicities (components i)) ∧
    (∀ i, T.weight i = AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentWeight
      f (components i)) ∧
    (∀ i, T.componentGenus i =
      Scheme.Hom.cohomologyFinrank
        (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component f (components i)).toSpecΓ
        (SheafOfModules.unit
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component f (components i)).ringCatSheaf :
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component f (components i)).Modules) 1) ∧
    (∀ i j, T.intersection i j =
      AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentDegree f (components i)
        (AlgebraicGeometry.Scheme.Hom.SpecialFiber.instIsProperComponentToResidueField
          f (components i))
        (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component_dimension_le_one
          C h_globalSections f genericFiberIso
          T.n components i)
        ((Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentInclusion f (components i))).obj
          (f.specialFiberComponent (components j)).associatedSheaf))

/-- The multiplicity coordinate of an associated numerical type is geometric. -/
theorem IsAssociatedTo.multiplicity_eq
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components) (i : Fin T.n) :
    T.multiplicity i = f.specialFiberMultiplicities (components i) := sorry

/-- The weight coordinate of an associated numerical type is the component global-sections degree. -/
theorem IsAssociatedTo.weight_eq
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components) (i : Fin T.n) :
    T.weight i = AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentWeight f (components i) := sorry

/-- The component-genus coordinate of an associated numerical type is geometric. -/
theorem IsAssociatedTo.componentGenus_eq
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components) (i : Fin T.n) :
    T.componentGenus i =
      Scheme.Hom.cohomologyFinrank
        (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component f (components i)).toSpecΓ
        (SheafOfModules.unit
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component f (components i)).ringCatSheaf :
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component f (components i)).Modules) 1 := sorry

/-- The intersection coordinate of an associated numerical type is a component divisor degree. -/
theorem IsAssociatedTo.intersection_eq
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components)
    (i j : Fin T.n) :
    T.intersection i j =
      AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentDegree f (components i)
        (AlgebraicGeometry.Scheme.Hom.SpecialFiber.instIsProperComponentToResidueField
          f (components i))
        (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component_dimension_le_one
          C h_globalSections f genericFiberIso
          T.n components i)
        ((Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentInclusion f (components i))).obj
          (f.specialFiberComponent (components j)).associatedSheaf) := sorry

end NumericalType

namespace AlgebraicGeometry.Scheme.Hom

open SpecialFiber

/-- Normalized degrees of component divisors reproduce the numerical Picard matrix. -/
theorem normalizedDegreeMap_componentPicardMap
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components) :
    (normalizedDegreeMap C h_globalSections f genericFiberIso T.n components).comp
        (componentPicardMap f T.n components).toAddMonoidHom =
      T.picardMap.toAddMonoidHom := sorry

/-- The kernel of generic-fibre restriction is contained in the kernel of the numerical quotient map. -/
theorem genericFiberPicardRestriction_ker_le
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components) :
    (genericFiberPicardRestriction f genericFiberIso).ker ≤
      (T.toPicardGroup.toAddMonoidHom.comp
        (normalizedDegreeMap C h_globalSections f genericFiberIso T.n components)).ker := sorry

/-- The canonical additive map from the generic-fibre Picard group to a numerical Picard group. -/
noncomputable def picardToNumerical
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components) :
    C.left.PicardGroup →+ T.PicardGroup :=
  AddMonoidHom.liftOfSurjective
    (genericFiberPicardRestriction f genericFiberIso)
    (genericFiberPicardRestriction_surjective π hπ C h_globalSections f genericFiberIso
      T.n components)
    ⟨T.toPicardGroup.toAddMonoidHom.comp
        (normalizedDegreeMap C h_globalSections f genericFiberIso T.n components),
      genericFiberPicardRestriction_ker_le π hπ C h_globalSections f genericFiberIso T components hT⟩

/-- The canonical numerical map is characterized by normalized degrees on restrictions. -/
theorem picardToNumerical_restrict
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components)
    (x : X.PicardGroup) :
    picardToNumerical π hπ C h_globalSections f genericFiberIso T components hT
        (genericFiberPicardRestriction f genericFiberIso x) =
      T.toPicardGroup
        (normalizedDegreeMap C h_globalSections f genericFiberIso T.n components x) := sorry

/-- The canonical numerical map is the unique homomorphism with the normalized-degree formula. -/
theorem existsUniquePicardToNumerical
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components) :
    ∃! φ : C.left.PicardGroup →+ T.PicardGroup,
      ∀ x : X.PicardGroup,
        φ (genericFiberPicardRestriction f genericFiberIso x) =
          T.toPicardGroup
            (normalizedDegreeMap C h_globalSections f genericFiberIso T.n components x) := sorry

/-- The kernel of the canonical numerical map consists of restrictions of componentwise degree-zero classes. -/
theorem picardToNumerical_ker_iff
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (π : R) (hπ : Irreducible π)
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (T : NumericalType)
    (components : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components)
    (y : C.left.PicardGroup) :
    y ∈ (picardToNumerical π hπ C h_globalSections f genericFiberIso T components hT).ker ↔
      ∃ x : X.PicardGroup,
        genericFiberPicardRestriction f genericFiberIso x = y ∧
          ∀ i : Fin T.n,
            componentDegree f (components i)
              (instIsProperComponentToResidueField f (components i))
              (component_dimension_le_one C h_globalSections f genericFiberIso T.n components i)
              ((Scheme.Modules.pullback (componentInclusion f (components i))).obj
                (Scheme.PicardGroup.repr x)) = 0 := sorry

end AlgebraicGeometry.Scheme.Hom
