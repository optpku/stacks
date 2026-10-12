/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.NumericalType.Genus
public import ReasLib.Algebra.Category.CommAlgCat.Module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.GenusFormula
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.IntersectionProperties
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace NumericalType

/-- A numerical type is the special-fibre type of a proper regular flat model with smooth,
geometrically integral one-dimensional generic fibre when its entries match the canonical
component multiplicities, residue-field degrees, component genera, and intersection degrees. -/
public def IsSpecialFiberType
    (T : NumericalType) (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (h_generic : Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      GeometricallyIntegral (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      topologicalKrullDim (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1) : Prop :=
  ∃ e : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)),
    let κ := (Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)
    let component (i : Fin T.n) :=
      (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubscheme (e i)
    let componentMap (i : Fin T.n) :=
      (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubschemeι (e i) ≫
        f.fiberToSpecResidueField (IsLocalRing.closedPoint R)
    let componentInclusion (i : Fin T.n) :=
      (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubschemeι (e i) ≫
        f.fiberι (IsLocalRing.closedPoint R)
    let structureSheaf (i : Fin T.n) : (component i).Modules :=
      SheafOfModules.unit (component i).ringCatSheaf
    let χ01 (i : Fin T.n) (L : (component i).Modules) : ℤ :=
      (Scheme.Hom.cohomologyFinrank (componentMap i) L 0 : ℤ) -
        (Scheme.Hom.cohomologyFinrank (componentMap i) L 1 : ℤ)
    (
      (∀ i, T.multiplicity i = f.specialFiberMultiplicities (e i)) ∧
      (∀ i, T.weight i =
        Module.finrank κ
          ((CommAlgCat.forgetToModule κ).obj (Scheme.Hom.globalSectionsAlg (componentMap i)))) ∧
      (∀ i, T.weight i * T.componentGenus i =
        Scheme.Hom.cohomologyFinrank (componentMap i) (structureSheaf i) 1) ∧
      (∀ i j, T.intersection i j =
        χ01 i ((Scheme.Modules.pullback (componentInclusion i)).obj
          (f.specialFiberComponent (e j)).associatedSheaf) - χ01 i (structureSheaf i)))

/-- The matching conditions in `IsSpecialFiberType` are exactly the displayed componentwise
equalities for one equivalence with the irreducible components of the special fibre. -/
public theorem isSpecialFiberType_iff
    (T : NumericalType) (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (h_generic : Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      GeometricallyIntegral (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      topologicalKrullDim (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1) :
    T.IsSpecialFiberType R K f h_generic ↔
      ∃ e : Fin T.n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)),
        let κ := (Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)
        let component (i : Fin T.n) :=
          (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubscheme (e i)
        let componentMap (i : Fin T.n) :=
          (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubschemeι (e i) ≫
            f.fiberToSpecResidueField (IsLocalRing.closedPoint R)
        let componentInclusion (i : Fin T.n) :=
          (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentSubschemeι (e i) ≫
            f.fiberι (IsLocalRing.closedPoint R)
        let structureSheaf (i : Fin T.n) : (component i).Modules :=
          SheafOfModules.unit (component i).ringCatSheaf
        let χ01 (i : Fin T.n) (L : (component i).Modules) : ℤ :=
          (Scheme.Hom.cohomologyFinrank (componentMap i) L 0 : ℤ) -
            (Scheme.Hom.cohomologyFinrank (componentMap i) L 1 : ℤ)
        (
          (∀ i, T.multiplicity i = f.specialFiberMultiplicities (e i)) ∧
          (∀ i, T.weight i =
            Module.finrank κ
              ((CommAlgCat.forgetToModule κ).obj
                (Scheme.Hom.globalSectionsAlg (componentMap i)))) ∧
          (∀ i, T.weight i * T.componentGenus i =
            Scheme.Hom.cohomologyFinrank (componentMap i) (structureSheaf i) 1) ∧
          (∀ i j, T.intersection i j =
            χ01 i ((Scheme.Modules.pullback (componentInclusion i)).obj
              (f.specialFiberComponent (e j)).associatedSheaf) - χ01 i (structureSheaf i))) := sorry

/-- A numerical type arising from such a special fibre has nonnegative genus. -/
public theorem genus_nonneg_of_isSpecialFiberType
    (T : NumericalType) (R K : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Flat f]
    [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (h_generic : Smooth (pullback.snd f
      (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      GeometricallyIntegral (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      topologicalKrullDim (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1)
    (hT : T.IsSpecialFiberType R K f h_generic) :
    0 ≤ T.genus := sorry

variable (R K : Type u)
variable [hCommRing : CommRing R] [hDomain : IsDomain R]
  [hDVR : IsDiscreteValuationRing R]
variable [hField : Field K] [hAlgebra : Algebra R K] [hFractionRing : IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)
variable (C : SchemeOverField K) [hCurve : Curve C] [hSmooth : Smooth C.hom]
  [hProjective : Projective C.hom] [hProperC : IsProper C.hom]
variable (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [hFlat : Flat f] [hFiniteType : Scheme.Hom.FiniteType f]
  [hProper : IsProper f] [hRegular : Scheme.Regular X]
variable (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))

section Construction

variable (h_component_proper :
  ∀ i, IsProper (SpecialFiber.componentToResidueField f (components i)))
variable (h_component_dimension :
  ∀ i, topologicalKrullDim (SpecialFiber.component f (components i)) ≤ 1)

include hCommRing hDomain hDVR hField hAlgebra hFractionRing hπ hCurve hSmooth
  hProjective hProperC h_globalSections hFlat hFiniteType hProper hRegular genericFiberIso
  components

/-- The special fibre in a proper regular model has at least one irreducible component. -/
theorem specialFiber_n_pos : 0 < n := sorry

/-- Every irreducible component of the special fibre has positive multiplicity. -/
theorem specialFiber_multiplicity_pos (i : Fin n) :
    0 < f.specialFiberMultiplicities (components i) := sorry

/-- The residue-field degree of every irreducible component is positive. -/
theorem specialFiber_weight_pos (i : Fin n) :
    0 < Module.finrank
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
      ((CommAlgCat.forgetToModule
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))).obj
        (Scheme.Hom.globalSectionsAlg
          (SpecialFiber.componentToResidueField f (components i)))) := sorry

/-- Pairwise component degrees give a symmetric intersection matrix. -/
theorem specialFiber_intersection_symmetric (i j : Fin n) :
    SpecialFiber.componentDegree f (components i) (h_component_proper i)
        (h_component_dimension i)
        ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
          (f.specialFiberComponent (components j)).associatedSheaf) =
      SpecialFiber.componentDegree f (components j) (h_component_proper j)
        (h_component_dimension j)
        ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components j))).obj
          (f.specialFiberComponent (components i)).associatedSheaf) := sorry

/-- Distinct special-fibre components have nonnegative intersection degree. -/
theorem specialFiber_intersection_offDiagonal_nonnegative
    (i j : Fin n) (hij : i ≠ j) :
    0 ≤ SpecialFiber.componentDegree f (components i) (h_component_proper i)
      (h_component_dimension i)
      ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
        (f.specialFiberComponent (components j)).associatedSheaf) := sorry

/-- Every nonempty proper family of special-fibre components meets its complement. -/
theorem specialFiber_intersection_connected
    (I : Set (Fin n)) (hI : I.Nonempty) (hI_ne : I ≠ Set.univ) :
    ∃ i ∈ I, ∃ j ∉ I,
      SpecialFiber.componentDegree f (components i) (h_component_proper i)
        (h_component_dimension i)
        ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
          (f.specialFiberComponent (components j)).associatedSheaf) ≠ 0 := sorry

/-- The multiplicity-weighted intersection degree with every component vanishes. -/
theorem specialFiber_rowSum_eq_zero (i : Fin n) :
    ∑ j,
      SpecialFiber.componentDegree f (components i) (h_component_proper i)
          (h_component_dimension i)
          ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
            (f.specialFiberComponent (components j)).associatedSheaf) *
        (f.specialFiberMultiplicities (components j) : ℤ) = 0 := sorry

/-- Each pairwise component degree is divisible by the corresponding residue-field degree. -/
theorem specialFiber_weight_dvd (i j : Fin n) :
    ((Module.finrank
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
      ((CommAlgCat.forgetToModule
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))).obj
        (Scheme.Hom.globalSectionsAlg
          (SpecialFiber.componentToResidueField f (components i)))) : ℤ) ∣
      SpecialFiber.componentDegree f (components i) (h_component_proper i)
        (h_component_dimension i)
        ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
          (f.specialFiberComponent (components j)).associatedSheaf)) := sorry

/-- The numerical type determined by the special fibre of a regular proper model. -/
public def ofSpecialFiber
    (h_component_proper :
      ∀ i, IsProper (SpecialFiber.componentToResidueField f (components i)))
    (h_component_dimension :
      ∀ i, topologicalKrullDim (SpecialFiber.component f (components i)) ≤ 1) : NumericalType :=
  NumericalType.of n
    (specialFiber_n_pos R K π hπ C h_globalSections f genericFiberIso n components)
    (fun i ↦ f.specialFiberMultiplicities (components i))
    (fun i ↦ Module.finrank
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
        ((CommAlgCat.forgetToModule
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))).obj
        (Scheme.Hom.globalSectionsAlg
          (SpecialFiber.componentToResidueField f (components i)))))
    (fun i ↦ Scheme.Hom.cohomologyFinrank
      (SpecialFiber.component f (components i)).toSpecΓ
      (SheafOfModules.unit
        (SpecialFiber.component f (components i)).ringCatSheaf :
        (SpecialFiber.component f (components i)).Modules) 1)
    (fun i j ↦ SpecialFiber.componentDegree f (components i) (h_component_proper i)
      (h_component_dimension i)
      ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
        (f.specialFiberComponent (components j)).associatedSheaf))
    (specialFiber_multiplicity_pos R K π hπ C h_globalSections f genericFiberIso n components
      )
    (specialFiber_weight_pos R K π hπ C h_globalSections f genericFiberIso n components)
    (specialFiber_intersection_symmetric R K π hπ C h_globalSections f genericFiberIso n
      components h_component_proper h_component_dimension)
    (specialFiber_intersection_offDiagonal_nonnegative R K π hπ C h_globalSections f
      genericFiberIso n components h_component_proper h_component_dimension)
    (specialFiber_intersection_connected R K π hπ C h_globalSections f genericFiberIso n
      components h_component_proper h_component_dimension)
    (specialFiber_rowSum_eq_zero R K π hπ C h_globalSections f genericFiberIso n components
      h_component_proper h_component_dimension)
    (specialFiber_weight_dvd R K π hπ C h_globalSections f genericFiberIso n components
      h_component_proper h_component_dimension)

/-- The special-fibre numerical type has the prescribed number of components. -/
public theorem ofSpecialFiber_n :
    (ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n components
      h_component_proper h_component_dimension).n = n := sorry

/-- The multiplicity projection of the special-fibre numerical type. -/
public theorem ofSpecialFiber_multiplicity (i : Fin n) :
    (ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n components
      h_component_proper h_component_dimension).multiplicity i =
      f.specialFiberMultiplicities (components i) := sorry

/-- The residue-field degree projection of the special-fibre numerical type. -/
public theorem ofSpecialFiber_weight (i : Fin n) :
    (ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n components
      h_component_proper h_component_dimension).weight i =
      Module.finrank
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
        ((CommAlgCat.forgetToModule
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))).obj
          (Scheme.Hom.globalSectionsAlg
            (SpecialFiber.componentToResidueField f (components i)))) := sorry

/-- The component-genus projection of the special-fibre numerical type. -/
public theorem ofSpecialFiber_componentGenus (i : Fin n) :
    (ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n components
      h_component_proper h_component_dimension).componentGenus i =
      Scheme.Hom.cohomologyFinrank
        (SpecialFiber.component f (components i)).toSpecΓ
        (SheafOfModules.unit
          (SpecialFiber.component f (components i)).ringCatSheaf :
          (SpecialFiber.component f (components i)).Modules) 1 := sorry

/-- The pairwise intersection projection of the special-fibre numerical type. -/
public theorem ofSpecialFiber_intersection (i j : Fin n) :
    (ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n components
      h_component_proper h_component_dimension).intersection i j =
      SpecialFiber.componentDegree f (components i) (h_component_proper i)
        (h_component_dimension i)
        ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
          (f.specialFiberComponent (components j)).associatedSheaf) := sorry

end Construction

/-- The genus of the numerical type determined by the special fibre equals the genus of the
smooth generic curve. -/
public theorem ofSpecialFiber_genus_eq :
    (ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n components
      (fun i ↦ inferInstance)
      (fun i ↦ SpecialFiber.component_dimension_le_one
        C h_globalSections f genericFiberIso n components i)).genus =
      (SchemeOverField.genus C
        (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections : ℤ) := sorry

end NumericalType
