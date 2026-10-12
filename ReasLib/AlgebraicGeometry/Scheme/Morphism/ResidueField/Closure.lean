/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.SeparableClosure
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.FieldTheory.Separable.Generated

/-!
# Relative closures of scheme residue fields

This leaf fixes the field-extension structures induced by a morphism to an affine field spectrum
and packages the associated algebraic and separable closure objects.  It deliberately sits above
the map-level residue-field owner, so ordinary residue-field morphisms do not import field theory.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.ResidueField

/-- The relative algebraic closure of `k` in the residue field at `x`, using the canonical
`k`-algebra structure induced by `f`. -/
noncomputable abbrev algebraicClosureOfSpec
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    @IntermediateField k (X.residueField x) _ _ (algebraOfSpec f x) :=
  @algebraicClosure k (X.residueField x) _ _ (algebraOfSpec f x)

/-- The relative separable closure of `k` in the residue field at `x`, using the canonical
`k`-algebra structure induced by `f`. -/
noncomputable abbrev separableClosureOfSpec
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :
    @IntermediateField k (X.residueField x) _ _ (algebraOfSpec f x) :=
  @separableClosure k (X.residueField x) _ _ (algebraOfSpec f x)

/-- The proposition that the residue field at `x` is algebraic over the base field through the
canonical map `mapOfSpec f x`. -/
abbrev IsAlgebraicOverSpec
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :=
  @Algebra.IsAlgebraic k (X.residueField x) _ _ (algebraOfSpec f x)

/-- The proposition that the residue field at `x` is separable, without an algebraicity
assumption, over the base field through the canonical algebra structure induced by `f`. -/
abbrev IsSeparableOverSpec
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) (x : X) :=
  @Algebra.IsSeparableOver k (X.residueField x) _ _ (algebraOfSpec f x)

/-- The relative algebraic closure of the residue field of `f x` in the residue field at `x`.
This is the closure object associated with the canonical `residueFieldAlgebra f x` instance. -/
noncomputable abbrev algebraicClosureOfResidueField
    {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    @IntermediateField (S.residueField (f x)) (X.residueField x) _ _
      (residueFieldAlgebra f x) :=
  @algebraicClosure (S.residueField (f x)) (X.residueField x) _ _
    (residueFieldAlgebra f x)

end AlgebraicGeometry.Scheme.Hom.ResidueField
