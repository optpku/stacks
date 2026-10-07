module

public import ReasLib.AlgebraicGeometry.NumericalType.SpecialFiber
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Field
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField.BaseField
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.GenusBound
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Intersection
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.SpecialFiber

section

variable (R K : Type u) [hCommRing : CommRing R] [hDomain : IsDomain R]
  [hDVR : IsDiscreteValuationRing R]
variable [hField : Field K] [hAlgebra : Algebra R K] [hFractionRing : IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)
variable (C : SchemeOverField K) [hCurve : Curve C] [hSmooth : Smooth C.hom]
  [hProjective : Projective C.hom]
variable (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [hFlat : Flat f] [hFiniteType : Scheme.Hom.FiniteType f]
  [hProper : IsProper f] [hRegular : Scheme.Regular X]
variable (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
variable (s : Spec ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) ⟶
  f.fiber (IsLocalRing.closedPoint R))
variable (h_section : s ≫ f.fiberToSpecResidueField (IsLocalRing.closedPoint R) = 𝟙 _)
variable (h_smooth : (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)).SmoothAt
  (s (IsLocalRing.closedPoint
    ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))))
variable (h_eq :
    NumericalType.topologicalGenus
        (NumericalType.ofSpecialFiber R K π hπ C h_globalSections f genericFiberIso n
          components (fun i ↦ instIsProperComponentToResidueField f (components i))
          (fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n
            components i)) +
      @GeometricGenus.ofScheme _ _
        (Over.mk (f.fiberToSpecResidueField (IsLocalRing.closedPoint R)) :
          SchemeOverField ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)))
        (fiberToSpecResidueField_isProper f (IsLocalRing.closedPoint R))
        (regularModel_specialFiber_dimension_le_one R K π hπ C h_globalSections f
          genericFiberIso) =
      cohomologyFinrank (Scheme.reductionι (f.fiber (IsLocalRing.closedPoint R)) ≫
        f.fiberToSpecResidueField (IsLocalRing.closedPoint R))
        (SheafOfModules.unit (Scheme.reduction (f.fiber (IsLocalRing.closedPoint R))).ringCatSheaf :
          Scheme.Modules (Scheme.reduction (f.fiber (IsLocalRing.closedPoint R)))) 1)

/-- Every reduced irreducible component of the closed fibre is integral. -/
instance componentIsIntegral (i : Fin n) :
    IsIntegral (component f (components i)) := sorry

/-- The global sections of an indexed proper integral component form a field. -/
@[implicit_reducible]
noncomputable instance componentGlobalSectionsField (i : Fin n) :
    Field (globalSectionsAlg (componentToResidueField f (components i))) :=
  @globalSectionsField _ _ _ (componentToResidueField f (components i))
    (componentIsIntegral R f n components i)
    (@IsProper.toUniversallyClosed _ _ _ (instIsProperComponentToResidueField f (components i)))

/-- The global-sections algebra of an indexed component is induced by its residue field. -/
@[implicit_reducible]
noncomputable instance componentGlobalSectionsAlgebra (i : Fin n) :
    Algebra ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
      (globalSectionsAlg (componentToResidueField f (components i))) :=
  globalSectionsAlgebra (componentToResidueField f (components i))

include hCommRing hDomain hDVR hField hAlgebra hFractionRing hπ hCurve hSmooth hProjective
  h_globalSections hFlat hFiniteType hProper hRegular genericFiberIso h_section h_smooth h_eq

/-- Equality in the genus bound identifies the unique component through the chosen smooth point. -/
theorem uniqueComponentContainingPoint :
    ∃! i : Fin n,
      s (IsLocalRing.closedPoint
        ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
          (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i) := sorry

/-- The component through the chosen smooth point is a curve over the residue field. -/
theorem componentContainingPointIsCurve (i : Fin n)
    (h_i_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i)) :
    Curve (Over.mk (componentToResidueField f (components i))) := sorry

/-- The component through the chosen smooth point is smooth over the residue field. -/
theorem componentContainingPointIsSmooth (i : Fin n)
    (h_i_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i)) :
    Smooth (componentToResidueField f (components i)) := sorry

/-- The component through the chosen smooth point is projective over the residue field. -/
theorem componentContainingPointIsProjective (i : Fin n)
    (h_i_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i)) :
    Projective (componentToResidueField f (components i)) := sorry

/-- The component through the chosen smooth point is geometrically irreducible. -/
theorem componentContainingPointIsGeometricallyIrreducible (i : Fin n)
    (h_i_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i)) :
    GeometricallyIrreducible (componentToResidueField f (components i)) := sorry

/-- The global-sections algebra of another component is finite-dimensional over the residue field. -/
theorem otherComponentSectionsFiniteDimensional (i j : Fin n)
    (h_i_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i))
    (h_ne : j ≠ i) :
    FiniteDimensional
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
      (globalSectionsAlg (componentToResidueField f (components j))) := sorry

/-- The global-sections algebra of another component is separable over the residue field. -/
theorem otherComponentSectionsSeparable (i j : Fin n)
    (h_i_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i))
    (h_ne : j ≠ i) :
    Algebra.IsSeparable
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
      (globalSectionsAlg (componentToResidueField f (components j))) := sorry

/-- Another component has a rational point over its global-sections field. -/
theorem otherComponentHasRationalPointOverSections (i j : Fin n)
    (h_i_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i))
    (h_ne : j ≠ i) :
    SchemeOverField.BaseField.hasRationalPoint
      (Over.mk (component f (components j)).toSpecΓ : SchemeOverField
        (globalSectionsAlg (componentToResidueField f (components j)))) := sorry

/-- Another component is smooth over its global-sections field. -/
theorem otherComponentSmoothOverSections (i j : Fin n)
    (h_i_mem : s (IsLocalRing.closedPoint
      ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))) ∈
        (f.fiber (IsLocalRing.closedPoint R)).irreducibleComponentClosed (components i))
    (h_ne : j ≠ i) :
    Smooth (component f (components j)).toSpecΓ := sorry

end

end AlgebraicGeometry.Scheme.Hom.SpecialFiber
