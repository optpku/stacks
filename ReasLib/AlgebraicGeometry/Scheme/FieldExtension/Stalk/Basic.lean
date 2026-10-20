/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stalk

/-!
# Points and stalks of field-extension base changes

This leaf owns the pointwise field-extension base-change data before any
closed-fibre quotient or localization comparison is formed.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Pullback
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Stalk

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- For a point of a field-extension base change, the induced map from the source stalk. -/
abbrev toSourceMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    X.presheaf.stalk (FieldExtension.toSource k K f y) ⟶
      (FieldExtension.baseChange k K f).presheaf.stalk y :=
  (FieldExtension.toSource k K f).stalkMap y

/-- The tensor product of residue fields associated to a point of a field-extension base change. -/
abbrev pointTensor
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) : CommRingCat :=
  (Triplet.ofPoint y).tensor

/-- The canonical map from the pullback-point tensor ring to the point residue field. -/
abbrev residueTensorMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    pointTensor k K f y ⟶
      (FieldExtension.baseChange k K f).residueField y :=
  ofPointTensor y

/-- The residue field of a point on a field-extension base change. -/
abbrev residueField
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) : CommRingCat :=
  (FieldExtension.baseChange k K f).residueField y

/-- The prime of the pullback-point tensor ring determined by a base-change point. -/
abbrev pointPrime
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    PrimeSpectrum (pointTensor k K f y) :=
  SpecOfPoint y

/-- The prime ideal of the pullback-point tensor ring determined by a base-change point. -/
abbrev pointPrimeIdeal
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Ideal (pointTensor k K f y) :=
  (pointPrime k K f y).asIdeal

namespace Source

/-- The canonical ground-field algebra on the source stalk. -/
noncomputable abbrev groundAlgebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra k (X.presheaf.stalk (FieldExtension.toSource k K f y)) :=
  Scheme.Hom.stalkAlgebraOverField f (FieldExtension.toSource k K f y)

/-- Typeclass bridge for the canonical ground-field algebra on the source stalk. -/
noncomputable instance instGroundAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra k (X.presheaf.stalk (FieldExtension.toSource k K f y)) :=
  groundAlgebra k K f y

end Source

namespace BaseChange

/-- The canonical `K`-algebra structure on a field-extension base-change stalk. -/
abbrev algebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra K ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  ((((FieldExtension.toBase k K f).stalkMap y).hom).comp
    (StructureSheaf.toStalk K ((FieldExtension.toBase k K f) y)).hom).toAlgebra

/-- Typeclass bridge for the canonical base-field algebra on a base-change stalk. -/
instance instAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra K ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  algebra k K f y

/-- The canonical ground-field algebra structure on a field-extension base-change stalk. -/
abbrev groundAlgebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra k ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  ((algebraMap K ((FieldExtension.baseChange k K f).presheaf.stalk y)).comp
    (algebraMap k K)).toAlgebra

/-- Typeclass bridge for the canonical ground-field algebra on a base-change stalk. -/
instance instGroundAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra k ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  groundAlgebra k K f y

/-- The ground-field action on a base-change stalk factors through `K`. -/
theorem groundTower
    (y : FieldExtension.baseChange k K f) :
    IsScalarTower k K ((FieldExtension.baseChange k K f).presheaf.stalk y) := sorry

/-- Typeclass bridge for the canonical base-change-stalk scalar tower. -/
instance instGroundTower
    (y : FieldExtension.baseChange k K f) :
    IsScalarTower k K ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  groundTower f y

/-- The residue field at the base coordinate of a field-extension base-change point maps
canonically to the extension field. -/
noncomputable abbrev residueMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    (Spec (CommRingCat.of K)).residueField ((FieldExtension.toBase k K f) y) →+* K :=
  ((Scheme.descResidueField
      (Scheme.stalkClosedPointTo (𝟙 (Spec (CommRingCat.of K))))).hom).comp
    ((Scheme.residueFieldCongr
      (Subsingleton.elim
        ((FieldExtension.toBase k K f) y)
        (IsLocalRing.closedPoint K))).hom).hom

end BaseChange

namespace Source

/-- The source-stalk map at a base-change point, regarded as a `k`-algebra map. -/
abbrev map
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    X.presheaf.stalk (FieldExtension.toSource k K f y) →ₐ[k]
      ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  { toRingHom := (FieldExtension.Stalk.toSourceMap k K f y).hom
    commutes' := sorry }

/-- The canonical algebra structure induced by the source-stalk map. -/
abbrev algebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra (X.presheaf.stalk (FieldExtension.toSource k K f y))
      ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  (map k K f y).toRingHom.toAlgebra

/-- Typeclass bridge for the source-stalk algebra on a base-change stalk. -/
instance instAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra (X.presheaf.stalk (FieldExtension.toSource k K f y))
      ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  algebra k K f y

end Source

/-- The tensor product of the source stalk with the extension field at a base-change point. -/
abbrev stalkTensor
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) : Type u :=
  X.presheaf.stalk (FieldExtension.toSource k K f y) ⊗[k] K

namespace Point

/-- The canonical map from the extension field to the pullback-point tensor ring. -/
abbrev baseMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    K →+* pointTensor k K f y :=
  ((Triplet.ofPoint y).tensorInr.hom).comp
    ((((Spec (CommRingCat.of K)).residue
      ((FieldExtension.toBase k K f) y)).hom).comp
        (StructureSheaf.toStalk K ((FieldExtension.toBase k K f) y)).hom)

/-- The canonical `K`-algebra structure on the pullback-point tensor ring. -/
abbrev baseAlgebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra K (pointTensor k K f y) :=
  (baseMap k K f y).toAlgebra

/-- Typeclass bridge for the canonical base-field action on the point tensor ring. -/
instance instBaseAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra K (pointTensor k K f y) :=
  baseAlgebra k K f y

/-- The canonical ground-field algebra structure induced through `K`. -/
abbrev groundAlgebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra k (pointTensor k K f y) :=
  ((baseMap k K f y).comp
    (algebraMap k K)).toAlgebra

/-- Typeclass bridge for the canonical ground-field action on the point tensor ring. -/
instance instGroundAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra k (pointTensor k K f y) :=
  groundAlgebra k K f y

/-- The ground-field action on the point tensor ring factors through `K`. -/
theorem groundTower
    (y : FieldExtension.baseChange k K f) :
    IsScalarTower k K (pointTensor k K f y) :=
  IsScalarTower.of_algebraMap_eq' rfl

/-- Typeclass bridge for the canonical point-tensor scalar tower. -/
instance instGroundTower
    (y : FieldExtension.baseChange k K f) :
    IsScalarTower k K (pointTensor k K f y) :=
  groundTower f y

end Point

namespace Tensor

/-- The canonical `k`-algebra map from the source stalk to the pullback-point tensor ring. -/
abbrev sourceMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    X.presheaf.stalk (FieldExtension.toSource k K f y) →ₐ[k]
      pointTensor k K f y :=
  { toRingHom := ((Triplet.ofPoint y).tensorInl.hom).comp
      (X.residue (FieldExtension.toSource k K f y)).hom
    commutes' := sorry }

/-- The map from the source-stalk tensor product to the pullback-point tensor ring. -/
abbrev pointMap
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    stalkTensor k K f y →ₐ[k] pointTensor k K f y :=
  Algebra.TensorProduct.productMap
    (sourceMap k K f y)
    (IsScalarTower.toAlgHom k K (pointTensor k K f y))

/-- The canonical algebra structure from the source-stalk tensor product to a base-change stalk. -/
noncomputable abbrev algebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra (stalkTensor k K f y)
      ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  (Algebra.TensorProduct.productMap
    (Source.map k K f y)
    (IsScalarTower.toAlgHom k K ((FieldExtension.baseChange k K f).presheaf.stalk y))).toRingHom.toAlgebra

/-- Typeclass bridge for the source-stalk tensor algebra on a base-change stalk. -/
noncomputable instance instAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra (stalkTensor k K f y)
      ((FieldExtension.baseChange k K f).presheaf.stalk y) :=
  algebra k K f y

/-- The prime of the source-stalk tensor product lying over a base-change point. -/
abbrev primeIdeal
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Ideal (stalkTensor k K f y) :=
  Ideal.comap
    (pointMap k K f y).toRingHom
    (pointPrimeIdeal k K f y)

end Tensor

namespace Residue

/-- The canonical `k`-algebra structure on the source residue field. -/
noncomputable abbrev sourceAlgebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra k (X.residueField (FieldExtension.toSource k K f y)) :=
  Scheme.Hom.ResidueField.algebraOfSpec f (FieldExtension.toSource k K f y)

/-- Typeclass bridge for the source residue-field algebra. -/
noncomputable instance instSourceAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra k (X.residueField (FieldExtension.toSource k K f y)) :=
  sourceAlgebra k K f y

/-- The canonical `K`-algebra structure on the base-change residue field. -/
noncomputable abbrev baseAlgebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra K ((FieldExtension.baseChange k K f).residueField y) :=
  Scheme.Hom.ResidueField.algebraOfSpec (FieldExtension.toBase k K f) y

/-- Typeclass bridge for the base-change residue-field algebra. -/
noncomputable instance instBaseAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra K ((FieldExtension.baseChange k K f).residueField y) :=
  baseAlgebra k K f y

/-- The residue field of a base-change point is an algebra over its point tensor ring. -/
abbrev tensorAlgebra
    (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (y : FieldExtension.baseChange k K f) :
    Algebra (pointTensor k K f y)
      (residueField k K f y) :=
  (residueTensorMap k K f y).hom.toAlgebra

/-- Typeclass bridge for the canonical point-tensor algebra on a base-change residue field. -/
instance instTensorAlgebra
    (y : FieldExtension.baseChange k K f) :
    Algebra (pointTensor k K f y)
      (residueField k K f y) :=
  tensorAlgebra k K f y

end Residue

end FieldExtension.Stalk

end AlgebraicGeometry
