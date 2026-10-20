/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Topology.Connected.Basic
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Basic

/-!
# Comparison maps for field-extension base changes

This leaf is independent of Galois theory.  A `k`-algebra embedding between two extension
fields induces a morphism between the corresponding pullbacks, together with the projection
formulas needed by downstream constructions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CommRingCat
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

namespace FieldExtension.Comparison

/-- The map `Spec L ⟶ Spec K` induced by a `k`-algebra homomorphism `K →ₐ[k] L`. -/
noncomputable abbrev baseMap
    {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (i : K →ₐ[k] L) :
    Spec (of L) ⟶ Spec (of K) :=
  Spec.map (ofHom i.toRingHom)

/-- The comparison base morphism lies over `Spec k`. -/
theorem baseMap_over
    {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L] (i : K →ₐ[k] L) :
    baseMap i ≫ FieldExtension.specMap k K =
      FieldExtension.specMap k L := sorry

/-- The comparison base morphism induced by the identity extension homomorphism is the identity.
-/
@[simp]
theorem baseMap_id
    {k K : Type u} [Field k] [Field K] [Algebra k K] :
    baseMap (AlgHom.id k K) = 𝟙 (Spec (of K)) := sorry

/-- Comparison base morphisms are contravariantly functorial in extension homomorphisms. -/
@[simp]
theorem baseMap_comp
    {k K L M : Type u} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    (i : K →ₐ[k] L) (j : L →ₐ[k] M) :
    baseMap (j.comp i) = baseMap j ≫ baseMap i := sorry

/-- The pullback morphism induced by a `k`-algebra embedding between extension fields. -/
noncomputable def hom
    {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L]
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) (i : K →ₐ[k] L) :
    FieldExtension.baseChange k L f ⟶ FieldExtension.baseChange k K f :=
  Scheme.AffineBaseChange.mapAlg f i

/-- The field-extension comparison morphism is compatible with the source projection. -/
theorem hom_toSource
    {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L]
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) (i : K →ₐ[k] L) :
    hom f i ≫ FieldExtension.toSource k K f =
      FieldExtension.toSource k L f := sorry

/-- The field-extension comparison morphism is compatible with the extension-base projections. -/
theorem hom_toBase
    {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L]
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) (i : K →ₐ[k] L) :
    hom f i ≫ FieldExtension.toBase k K f =
      FieldExtension.toBase k L f ≫ baseMap i := sorry

/-- The comparison morphism induced by the identity extension homomorphism is the identity. -/
@[simp]
theorem hom_id
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) :
    hom f (AlgHom.id k K) = 𝟙 (FieldExtension.baseChange k K f) := sorry

/-- Comparison morphisms are contravariantly functorial in extension homomorphisms. -/
@[simp]
theorem hom_comp
    {k K L M : Type u} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    {X : Scheme.{u}} (f : X ⟶ Spec (of k))
    (i : K →ₐ[k] L) (j : L →ₐ[k] M) :
    hom f (j.comp i) = hom f j ≫ hom f i := sorry

/-- The induced map on connected components of two field-extension base changes. -/
noncomputable abbrev connectedComponentsMap
    {k K L : Type u} [Field k] [Field K] [Field L]
    [Algebra k K] [Algebra k L]
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) (i : K →ₐ[k] L) :
    ConnectedComponents (FieldExtension.baseChange k L f) →
      ConnectedComponents (FieldExtension.baseChange k K f) :=
  Continuous.connectedComponentsMap (hom f i).continuous

/-- The connected-components comparison induced by the identity extension homomorphism is the
identity function. -/
@[simp]
theorem connectedComponentsMap_id
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (of k)) :
    connectedComponentsMap f (AlgHom.id k K) = id := sorry

/-- Connected-components comparison maps are contravariantly functorial in extension
homomorphisms. -/
@[simp]
theorem connectedComponentsMap_comp
    {k K L M : Type u} [Field k] [Field K] [Field L] [Field M]
    [Algebra k K] [Algebra k L] [Algebra k M]
    {X : Scheme.{u}} (f : X ⟶ Spec (of k))
    (i : K →ₐ[k] L) (j : L →ₐ[k] M) :
    connectedComponentsMap f (j.comp i) =
      connectedComponentsMap f i ∘ connectedComponentsMap f j := sorry

end FieldExtension.Comparison

end AlgebraicGeometry
