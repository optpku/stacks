module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

/-!
# Residue fields on fibres of scheme morphisms

This leaf specializes the residue-field algebra API to points of a fibre. It
depends on the fibre construction, while the general morphism API remains in
`Scheme.Morphism.ResidueField`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The residue field of a point of the fibre `X_s` has its canonical algebra structure over the
residue field `κ(s)` of the base point. -/
noncomputable instance fiberResidueFieldAlgebra
    {X S : Scheme.{u}} (f : X ⟶ S) (s : S) (x : f.fiber s) :
    Algebra (S.residueField s) ((f.fiber s).residueField x) :=
  ResidueField.algebraOfSpec (f.fiberToSpecResidueField s) x

/-- The structure morphism of a scheme-theoretic fibre is locally of finite type
when the ambient morphism is. -/
instance instLocallyOfFiniteType_fiberToSpecResidueField
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
  inferInstanceAs (LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s)))

end AlgebraicGeometry.Scheme.Hom

namespace AlgebraicGeometry.Scheme

/-- The spectrum of the residue field of any scheme point is `T₁`. -/
instance instT1Space_specResidueField {X : Scheme.{u}} (x : X) :
    T1Space (Spec (X.residueField x)) := sorry

end AlgebraicGeometry.Scheme
