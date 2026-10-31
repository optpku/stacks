/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Affine base change of schemes and modules

This leaf owns the pullback of a scheme over `Spec A` along an arbitrary
commutative-algebra map `A → B`, together with its two projections and the
pullback of a module sheaf. Field-extension base change is a specialization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.AffineBaseChange

/-- The affine scheme morphism `Spec B ⟶ Spec A` induced by a commutative-algebra map `A → B`.
-/
abbrev specMap
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A B))

/-- The affine base change of `f : X ⟶ Spec A` along the algebra map `A → B`. -/
abbrev baseChange
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) : Scheme.{u} :=
  pullback f (specMap A B)

/-- The projection from an affine base change back to the original scheme. -/
abbrev toSource
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) :
    baseChange A B f ⟶ X :=
  pullback.fst f (specMap A B)

/-- The projection from an affine base change to the new affine base `Spec B`. -/
abbrev toBase
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) :
    baseChange A B f ⟶ Spec (CommRingCat.of B) :=
  pullback.snd f (specMap A B)

/-- The affine spectrum maps of a compatible algebra tower compose to the direct spectrum map. -/
@[reassoc, simp]
theorem specMap_comp
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    specMap B C ≫ specMap A B = specMap A C := by
  dsimp only [specMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← IsScalarTower.algebraMap_eq A B C]

/-- The spectrum map `Spec C ⟶ Spec B` in a compatible algebra tower, regarded as a morphism over
`Spec A`. -/
noncomputable def specMapOverBase
    (A B C : Type u) [Field A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (Over.mk (specMap A C) : SchemeOverField A) ⟶
      (Over.mk (specMap A B) : SchemeOverField A) :=
  Over.homMk (specMap B C) (specMap_comp A B C)

/-- The underlying scheme morphism of `specMapOverBase` is the spectrum map for `C/B`. -/
theorem specMapOverBase_left
    (A B C : Type u) [Field A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] :
    (specMapOverBase A B C).left = specMap B C := by
  rfl

/-- The iterated affine base change along a compatible algebra tower is canonically isomorphic
to the direct base change. -/
noncomputable def iteratedIso
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) :
    baseChange B C (toBase A B f) ≅ baseChange A C f :=
  (pullbackLeftPullbackSndIso f (specMap A B) (specMap B C)) ≪≫
    pullback.congrHom rfl (specMap_comp A B C)

/-- The tower base-change isomorphism commutes with the projection to the original scheme. -/
@[reassoc (attr := simp)]
theorem iteratedIso_hom_toSource
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) :
    (iteratedIso A B C f).hom ≫ toSource A C f =
      toSource B C (toBase A B f) ≫ toSource A B f := by
  simp [iteratedIso, toSource, pullback.congrHom_hom, Category.assoc,
    pullback.map, pullback.lift_fst]

/-- The tower base-change isomorphism commutes with the projection to the final affine base. -/
@[reassoc (attr := simp)]
theorem iteratedIso_hom_toBase
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) :
    (iteratedIso A B C f).hom ≫ toBase A C f =
      toBase B C (toBase A B f) := by
  simp [iteratedIso, toBase, pullback.congrHom_hom, Category.assoc,
    pullback.map, pullback.lift_snd]

/-- The morphism between affine base changes induced by a compatible map `B → C`. -/
noncomputable def map
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : B →+* C)
    (hg : algebraMap A C = g.comp (algebraMap A B)) :
    baseChange A C f ⟶ baseChange A B f :=
  let hMap :
      specMap A C = Spec.map (CommRingCat.ofHom g) ≫ specMap A B :=
    Eq.trans
      (congrArg (fun φ ↦ Spec.map (CommRingCat.ofHom φ)) hg)
      (Eq.trans
        (congrArg Spec.map (CommRingCat.ofHom_comp (algebraMap A B) g))
        (Spec.map_comp (CommRingCat.ofHom (algebraMap A B)) (CommRingCat.ofHom g)))
  pullback.map
    f
    (specMap A C)
    f
    (specMap A B)
    (𝟙 X)
    (Spec.map (CommRingCat.ofHom g))
    (𝟙 (Spec (CommRingCat.of A)))
    ((Category.id_comp f).trans (Category.comp_id f).symm)
    ((Category.comp_id (specMap A C)).trans hMap)

/-- Identifying an iterated affine base change with the direct one and then comparing it back to
the intermediate base change is the first projection of the iterated pullback. -/
@[reassoc (attr := simp)]
theorem iteratedIso_hom_map
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) :
    (iteratedIso A B C f).hom ≫
        map f (algebraMap B C) (IsScalarTower.algebraMap_eq A B C) =
      toSource B C (toBase A B f) := by
  apply pullback.hom_ext
  · change ((iteratedIso A B C f).hom ≫
        map f (algebraMap B C) (IsScalarTower.algebraMap_eq A B C)) ≫
          toSource A B f = toSource B C (toBase A B f) ≫ toSource A B f
    simpa [map, toSource, Category.assoc, pullback.map, pullback.lift_fst] using
      iteratedIso_hom_toSource A B C f
  · change ((iteratedIso A B C f).hom ≫
        map f (algebraMap B C) (IsScalarTower.algebraMap_eq A B C)) ≫
          toBase A B f = toSource B C (toBase A B f) ≫ toBase A B f
    calc
      _ = (iteratedIso A B C f).hom ≫ toBase A C f ≫ specMap B C := by
        simp [map, toBase, Category.assoc, pullback.map, pullback.lift_snd]
      _ = toBase B C (toBase A B f) ≫ specMap B C := by
        rw [← Category.assoc, iteratedIso_hom_toBase]
      _ = toSource B C (toBase A B f) ≫ toBase A B f := pullback.condition.symm

/-- The affine base-change comparison induced by an `A`-algebra homomorphism `B →ₐ[A] C`.

This is the preferred entry point when the compatibility with the base algebra is already
bundled in an `AlgHom`; `map` remains the lower-level `RingHom` interface. -/
noncomputable def mapAlg
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : B →ₐ[A] C) :
    baseChange A C f ⟶ baseChange A B f :=
  map f g.toRingHom (RingHom.ext fun x ↦ (g.commutes x).symm)

/-- An affine base-change comparison morphism commutes with the source projection. -/
theorem map_toSource
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : B →+* C)
    (hg : algebraMap A C = g.comp (algebraMap A B)) :
    map f g hg ≫ toSource A B f = toSource A C f := by
  simp [map, toSource, pullback.map, pullback.lift_fst]

/-- An affine base-change comparison morphism commutes with the projection to the affine base. -/
theorem map_toBase
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : B →+* C)
    (hg : algebraMap A C = g.comp (algebraMap A B)) :
    map f g hg ≫ toBase A B f =
      toBase A C f ≫ Spec.map (CommRingCat.ofHom g) := by
  simp [map, toBase, pullback.map, pullback.lift_snd]

/-- The `mapAlg` comparison commutes with the source projection. -/
theorem mapAlg_toSource
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : B →ₐ[A] C) :
    mapAlg f g ≫ toSource A B f = toSource A C f := by
  exact map_toSource f g.toRingHom _

/-- The `mapAlg` comparison commutes with the affine-base projection. -/
theorem mapAlg_toBase
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (g : B →ₐ[A] C) :
    mapAlg f g ≫ toBase A B f =
      toBase A C f ≫ Spec.map (CommRingCat.ofHom g.toRingHom) := by
  exact map_toBase f g.toRingHom _

end Scheme.AffineBaseChange

namespace Scheme.Modules.AffineBaseChange

/-- The pullback of a scheme module to an affine base change. -/
abbrev baseChange
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (L : X.Modules) :
    (Scheme.AffineBaseChange.baseChange A B f).Modules :=
  Scheme.Modules.baseChangeModule f (Scheme.AffineBaseChange.specMap A B) L

end Scheme.Modules.AffineBaseChange

end AlgebraicGeometry
