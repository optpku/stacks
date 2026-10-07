module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.ClosedFiber
public import ReasLib.AlgebraicGeometry.Scheme.Pullback.ResidueField

/-!
# Local properties of field-extension base-change stalks

This leaf records the reusable local, residue-field, and localization facts for
the pointwise field-extension base-change data.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Stalk.Local

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- The stalk map from a source scheme to a field-extension base change is local. -/
@[stacks 0C4Y]
theorem toSourceMap_isLocal
    (y : FieldExtension.baseChange k K f) :
    IsLocalHom (FieldExtension.Stalk.toSourceMap k K f y).hom := sorry

/-- The stalk map from a source scheme to a field-extension base change is faithfully flat. -/
@[stacks 0C4Y]
theorem toSourceMap_faithfullyFlat
    (y : FieldExtension.baseChange k K f) :
    RingHom.FaithfullyFlat
      (FieldExtension.Stalk.toSourceMap k K f y).hom := sorry

/-- The pullback-point prime is the kernel of the map to the point residue field. -/
@[stacks 0C4Y]
theorem pointPrime_asIdeal
    (y : FieldExtension.baseChange k K f) :
    FieldExtension.Stalk.pointPrimeIdeal k K f y =
      RingHom.ker (FieldExtension.Stalk.residueTensorMap k K f y).hom := sorry

/-- The comparison map from the associated point-tensor prime residue field to `κ(y)`. -/
@[stacks 0C4Y]
noncomputable abbrev pointPrime_residueFieldMap
  (y : FieldExtension.baseChange k K f) :
    (FieldExtension.Stalk.pointPrimeIdeal k K f y).ResidueField →+*
      FieldExtension.Stalk.residueField k K f y :=
  (Scheme.Pullback.SpecOfPoint.residueFieldMap y).hom

/-- The point-prime residue-field comparison map is bijective. -/
@[stacks 0C4Y]
theorem pointPrime_residueFieldMap_bijective
    (y : FieldExtension.baseChange k K f) :
    Function.Bijective
      (pointPrime_residueFieldMap f y) := sorry

/-- The base-change stalk is the localization of the source-stalk tensor product at its point prime. -/
@[stacks 0C4Y]
theorem stalk_isLocalizationAtPrime
    (y : FieldExtension.baseChange k K f) :
    IsLocalization.AtPrime
      ((FieldExtension.baseChange k K f).presheaf.stalk y)
      (FieldExtension.Stalk.Tensor.primeIdeal k K f y) := sorry

/-- The closed fibre is the localization of the point tensor ring at its point prime. -/
@[stacks 0C4Y]
theorem closedFiber_isLocalizationAtPrime
    (y : FieldExtension.baseChange k K f) :
    IsLocalization.AtPrime
      (FieldExtension.Stalk.ClosedFiber.quotient k K f y)
      (FieldExtension.Stalk.pointPrimeIdeal k K f y) := sorry

end FieldExtension.Stalk.Local

end AlgebraicGeometry
