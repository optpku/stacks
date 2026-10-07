module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein.Proper
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.Integral
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A proper morphism from a reduced scheme to an integral normal scheme has trivial
relative normalization when its generic points dominate and its generic fibre has only
the base field as global sections. -/
theorem isIso_fromNormalization_of_genericFiberGlobalSections
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsIntegral S] (hS : S.isNormal) [IsReduced X]
    (h_generic : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : Function.Bijective
      (globalSectionsMap (f.fiberToSpecResidueField (genericPoint S)))) :
    IsIso f.fromNormalization := sorry

/-- Under the normal-base generic-fibre criterion, the canonical map from the base
structure sheaf to the pushforward of the source structure sheaf is an isomorphism. -/
theorem structureSheafMap_isIso_of_genericFiberGlobalSections
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsIntegral S] (hS : S.isNormal) [IsReduced X]
    (h_generic : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : Function.Bijective
      (globalSectionsMap (f.fiberToSpecResidueField (genericPoint S)))) :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toShHom) := sorry

/-- A proper morphism satisfying the normal-base generic-fibre criterion has
geometrically connected fibres. -/
theorem geometricallyConnected_of_genericFiberGlobalSections
    {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [IsIntegral S] (hS : S.isNormal) [IsReduced X]
    (h_generic : ∀ x : X, x ∈ genericPoints X → f x = genericPoint S)
    (hΓ : Function.Bijective
      (globalSectionsMap (f.fiberToSpecResidueField (genericPoint S)))) :
    GeometricallyConnected f := sorry

end AlgebraicGeometry.Scheme.Hom
