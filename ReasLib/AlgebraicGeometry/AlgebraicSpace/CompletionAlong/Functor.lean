/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.IsoOverOpen
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.RigEtaleOver
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.RigEtale

/-!
# Completion of morphisms isomorphic over an open complement

Completion along a closed subset sends locally of finite type morphisms that
are isomorphisms over its complement to rig-étale morphisms of locally
Noetherian formal algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace TopologicalSpace TypeCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace completionAlong

/-- The source category `C_{X,T}` of morphisms `f : X' ⟶ X` that are locally of
finite type and isomorphisms over the open complement of `T`. -/
abbrev Source {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :=
  LocallyOfFiniteTypeIsoOverOpen (openComplementι X T)

/-- The target category of morphisms `g : W ⟶ X_/T` of formal algebraic spaces
with `W` locally Noetherian and `g` rig-étale. -/
abbrev Target {S : Scheme.{u}} (X : AlgebraicSpace S) (T : Closeds (Points X)) :=
  FormalAlgebraicSpace.LocallyNoetherianRigEtaleOver (completionAlong X T)

/-- Completing a locally-of-finite-type morphism that is an isomorphism over the
open complement of `T` yields a rig-étale morphism of formal algebraic spaces. -/
instance instRigEtale_map {S : Scheme.{u}} {X' X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (f : X' ⟶ X) (T : Closeds (Points X))
    [LocallyOfFiniteType f] [IsIso (openInverseImageTo f (openComplementι X T))] :
    FormalAlgebraicSpace.RigEtale (map f T) :=
  by
    refine @rigEtale_completionAlongMap S X X' inferInstance f inferInstance T ?_
    rw [Open.complementComparison_eq]
    exact Etale.of_isIso (openInverseImageTo f (openComplementι X T))

/-- An over-morphism sends sections supported over a closed subset to sections
supported over that same closed subset. -/
theorem mapOver_mem {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X))
    {Y Y' : Over X} (φ : Y ⟶ Y') (U : (Over S)ᵒᵖ)
    (x : (completionAlong Y.left (T.preimage (Points.continuous_map Y.hom))).obj U) :
    mapsInto (T.preimage (Points.continuous_map Y'.hom) : Set (Points Y'.left))
      (φ.left.app U x.1) :=
  sorry

/-- The morphism of completions over `X` induced by a morphism in `Over X`. -/
def mapOver {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X))
    {Y Y' : Over X} (φ : Y ⟶ Y') :
    completionAlong Y.left (T.preimage (Points.continuous_map Y.hom)) ⟶
      completionAlong Y'.left (T.preimage (Points.continuous_map Y'.hom)) where
  app U := ofHom fun x ↦ ⟨φ.left.app U x.1, mapOver_mem T φ U x⟩
  naturality := sorry

/-- The morphism of completions along `T` induced by a morphism of algebraic
spaces over `X`. -/
def mapOverHom {S : Scheme.{u}} {X Y Y' : AlgebraicSpace S} (T : Closeds (Points X))
    (hY : Y ⟶ X) (hY' : Y' ⟶ X) (φ : Y' ⟶ Y) (hφ : φ ≫ hY = hY') :
    completionAlong Y' (T.preimage (Points.continuous_map hY')) ⟶
      completionAlong Y (T.preimage (Points.continuous_map hY)) :=
  mapOver T (Over.homMk φ hφ : Over.mk hY' ⟶ Over.mk hY)

/-- Postcomposing `mapOver T φ` with `completionAlong.map Y'.hom T` recovers
`completionAlong.map Y.hom T`. -/
theorem mapOver_comp_map {S : Scheme.{u}} {X : AlgebraicSpace S} (T : Closeds (Points X))
    {Y Y' : Over X} (φ : Y ⟶ Y') :
    mapOver T φ ≫ map Y'.hom T = map Y.hom T :=
  sorry

/-- The object of `Target X T` obtained by completing a source morphism along
`T`. -/
def functorObj {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (T : Closeds (Points X)) (Y : Source X T) : Target X T where
  obj := Over.mk (map Y.obj.hom T)
  property := sorry

/-- The morphism of `Target X T` obtained by completing a morphism of source
objects along `T`. -/
def functorMap {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (T : Closeds (Points X)) {Y Y' : Source X T} (φ : Y ⟶ Y') :
    functorObj T Y ⟶ functorObj T Y' :=
  ObjectProperty.homMk (Over.homMk (mapOver T φ.hom) (mapOver_comp_map T φ.hom))

/-- Completing identity morphisms in `Source X T` yields identity morphisms. -/
theorem functorMap_id {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (T : Closeds (Points X)) (Y : Source X T) :
    functorMap T (𝟙 Y) = 𝟙 (functorObj T Y) :=
  sorry

/-- Completing composites in `Source X T` yields composites. -/
theorem functorMap_comp {S : Scheme.{u}} {X : AlgebraicSpace S} [IsLocallyNoetherian X]
    (T : Closeds (Points X)) {Y Y' Y'' : Source X T} (φ : Y ⟶ Y') (ψ : Y' ⟶ Y'') :
    functorMap T (φ ≫ ψ) = functorMap T φ ≫ functorMap T ψ :=
  sorry

end completionAlong

/-- Completion along a closed subset sends locally of finite type morphisms
isomorphic over its complement to locally Noetherian rig-étale formal spaces. -/
def completionFunctor {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]
    (T : Closeds (Points X)) : completionAlong.Source X T ⥤ completionAlong.Target X T where
  obj := completionAlong.functorObj T
  map := completionAlong.functorMap T
  map_id := completionAlong.functorMap_id T
  map_comp := completionAlong.functorMap_comp T

/-- The structure morphism of a completed object is the canonical completion map. -/
theorem completionFunctor_obj {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X))
    (Y : completionAlong.Source X T) :
    ((completionFunctor X T).obj Y).obj.hom = completionAlong.map Y.obj.hom T :=
  rfl

/-- Completion sends an over-morphism to its induced morphism on completions. -/
theorem completionFunctor_map {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsLocallyNoetherian X] (T : Closeds (Points X))
    {Y Y' : completionAlong.Source X T} (φ : Y ⟶ Y') :
    (((completionFunctor X T).map φ).hom).left = completionAlong.mapOver T φ.hom :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
