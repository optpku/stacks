module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType

/-!
# Varieties over a field

This leaf owns the standard typeclass for an integral, separated, finite-type
scheme over a field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

namespace Scheme.Hom

/-- A scheme morphism has variety fibers when every residue-field fiber is integral, separated,
and of finite type over its residue field. -/
def HasVarietyFibers {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  ∀ s : S, IsIntegral (f.fiber s) ∧ IsSeparated (f.fiberToSpecResidueField s) ∧
    Scheme.Hom.FiniteType (f.fiberToSpecResidueField s)

end Scheme.Hom

/-- A variety over the field `k` is a scheme `X` over `k` such that `X` is integral and the
structure morphism `X ⟶ Spec k` is separated and of finite type. -/
@[stacks 020D]
class Variety (X : Over (Spec (CommRingCat.of k))) : Prop extends
    IsIntegral X.left, IsSeparated X.hom, Scheme.Hom.FiniteType X.hom

/-- An integral scheme with separated, finite-type structure morphism over a field is a variety. -/
@[stacks 020D, instance]
instance instVariety (X : Over (Spec (CommRingCat.of k))) [h_integral : IsIntegral X.left]
    [h_separated : IsSeparated X.hom] [h_finiteType : FiniteType X.hom] : Variety X where
  toIsIntegral := h_integral
  toIsSeparated := h_separated
  toFiniteType := h_finiteType

/-- A variety over `k` is integral as a scheme. -/
@[stacks 020D, instance]
instance instIsIntegralLeftOfVariety (X : Over (Spec (CommRingCat.of k))) [h : Variety X] :
    IsIntegral X.left :=
  h.toIsIntegral

/-- A variety over `k` has separated structure morphism to `Spec k`. -/
@[stacks 020D, instance]
instance instIsSeparatedHomOfVariety (X : Over (Spec (CommRingCat.of k))) [h : Variety X] :
    IsSeparated X.hom :=
  h.toIsSeparated

/-- A variety over `k` is of finite type over `Spec k`. -/
@[stacks 020D, instance]
instance instFiniteTypeHomOfVariety (X : Over (Spec (CommRingCat.of k))) [h : Variety X] :
    FiniteType X.hom :=
  h.toFiniteType

/-- Unfold `Variety X` into integrality of `X` together with separatedness and finite type of the
structure morphism `X ⟶ Spec k`. -/
theorem variety_iff (X : Over (Spec (CommRingCat.of k))) :
    Variety X ↔ IsIntegral X.left ∧ IsSeparated X.hom ∧ Scheme.Hom.FiniteType X.hom := sorry

end AlgebraicGeometry
