/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.MorphismDifferentials
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Local

/-!
# Local criteria for unramified morphisms

This file characterizes unramifiedness at a point using the residue-field fibre, stalks of
relative differentials, the cotangent space, and the induced extension of residue fields.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} (f : X ⟶ S) (x : X)

/-- The local residue criterion asserting equality of the extended maximal ideal with the
maximal ideal of the source stalk and that the induced residue-field extension is finite and
separable. -/
def MaximalIdealResidueFieldUnramifiedAtCriterion : Prop :=
  Ideal.map (CommRingCat.Hom.hom (f.stalkMap x))
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
    FiniteDimensional (S.residueField (f x)) (X.residueField x) ∧
    Algebra.IsSeparable (S.residueField (f x)) (X.residueField x)

/-- The maximal-ideal and residue-field criterion is the conjunction of maximal-ideal equality,
finite-dimensionality, and separability of the induced residue-field extension. -/
theorem maximalIdealResidueFieldUnramifiedAtCriterion_iff :
    MaximalIdealResidueFieldUnramifiedAtCriterion f x ↔
      Ideal.map (CommRingCat.Hom.hom (f.stalkMap x))
          (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))) =
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) ∧
        FiniteDimensional (S.residueField (f x)) (X.residueField x) ∧
        Algebra.IsSeparable (S.residueField (f x)) (X.residueField x) :=
  Iff.rfl

/-- For a locally finite type morphism, unramifiedness at a point is equivalent to
unramifiedness of the residue-field fibre, vanishing of the global and fibre differential
stalks, vanishing of the cotangent space, and the maximal-ideal and finite separable
residue-field criterion. -/
theorem unramifiedAt_tfae_differentials_fiber_residueField
    [LocallyOfFiniteType f] :
    List.TFAE [
      f.UnramifiedAt x,
      (f.fiberToSpecResidueField (f x)).UnramifiedAt (f.asFiber x),
      IsZero (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x),
      IsZero
        (RingedSpace.stalkModuleCat
          (Ω[(f.fiberToSpecResidueField (f x)).toShHom]) (f.asFiber x)),
      Subsingleton
        ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[(X.presheaf.stalk x)]
          (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)),
      MaximalIdealResidueFieldUnramifiedAtCriterion f x] := sorry

/-- For a locally finite presentation morphism, G-unramifiedness at a point is equivalent to
ordinary unramifiedness of the residue-field fibre, vanishing of the global and fibre
differential stalks, vanishing of the cotangent space, and the maximal-ideal and finite
separable residue-field criterion. -/
theorem gUnramifiedAt_tfae_differentials_fiber_residueField
    [LocallyOfFinitePresentation f] :
    List.TFAE [
      f.GUnramifiedAt x,
      (f.fiberToSpecResidueField (f x)).UnramifiedAt (f.asFiber x),
      IsZero (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x),
      IsZero
        (RingedSpace.stalkModuleCat
          (Ω[(f.fiberToSpecResidueField (f x)).toShHom]) (f.asFiber x)),
      Subsingleton
        ((IsLocalRing.ResidueField (X.presheaf.stalk x)) ⊗[(X.presheaf.stalk x)]
          (RingedSpace.stalkModuleCat (Ω[f.toShHom]) x)),
      MaximalIdealResidueFieldUnramifiedAtCriterion f x] := sorry

namespace Scheme.Hom

/-- For a locally finite-type morphism to a locally Noetherian scheme, unramifiedness at a
point is equivalent to the maximal-ideal and finite separable residue-field criterion. -/
theorem unramifiedAt_iff_localRingCriterion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f]
    (x : X) :
    f.UnramifiedAt x ↔ MaximalIdealResidueFieldUnramifiedAtCriterion f x := sorry

/-- A locally finite-type morphism to a locally Noetherian scheme is unramified exactly when
the maximal-ideal and finite separable residue-field criterion holds at every source point. -/
theorem unramified_iff_forall_localRingCriterion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian Y] [LocallyOfFiniteType f] :
    Unramified f ↔ ∀ x : X, MaximalIdealResidueFieldUnramifiedAtCriterion f x := sorry

end Scheme.Hom

end AlgebraicGeometry
