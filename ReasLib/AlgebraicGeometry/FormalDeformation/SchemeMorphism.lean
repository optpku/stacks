/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Over

/-!
# Flat scheme morphisms over Artinian local algebras

Objects are scheme morphisms whose source and target are flat over an Artinian
local algebra. Morphisms consist of a base algebra map and contravariant scheme
maps forming two cartesian squares. The projection is cofibered in groupoids,
and its residue-object slices give deformation categories.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

noncomputable section

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeMorphismCat

variable {Λ k}

/-- The spectrum of the carrier of an Artinian local algebra. -/
abbrev specObj (A : ArtinianLocalAlgCat Λ k) : Scheme.{u} :=
  Spec (CommRingCat.of A.carrier)

/-- The contravariant spectrum map induced by an Artinian local algebra map. -/
def specMap {A B : ArtinianLocalAlgCat Λ k} (baseMap : A ⟶ B) :
    specObj B ⟶ specObj A :=
  Spec.map (CommRingCat.ofHom (ArtinianLocalAlgCat.Hom.toRingHom baseMap))

/-- The spectrum map of an identity algebra map is the identity. -/
theorem specMap_id (A : ArtinianLocalAlgCat Λ k) :
    specMap (𝟙 A) = 𝟙 (specObj A) := sorry

/-- The spectrum map reverses composition of algebra maps. -/
theorem specMap_comp {A B C : ArtinianLocalAlgCat Λ k} (baseMap : A ⟶ B)
    (nextMap : B ⟶ C) :
    specMap (baseMap ≫ nextMap) = specMap nextMap ≫ specMap baseMap := sorry

/-- Every scheme morphism to the spectrum of a field is flat. -/
theorem flat_over_field {K : Type u} [Field K] {X : Scheme.{u}}
    (structureHom : X ⟶ Spec (CommRingCat.of K)) :
    AlgebraicGeometry.Flat structureHom := sorry

end FlatSchemeMorphismCat

/-- Scheme morphisms over an Artinian local algebra with flat source and target. -/
def FlatSchemeMorphismCat :=
  Σ base : ArtinianLocalAlgCat Λ k, Σ source : Scheme.{u}, Σ target : Scheme.{u},
    Σ hom : source ⟶ target, Σ sourceOver : source ⟶ FlatSchemeMorphismCat.specObj base,
      {targetOver : target ⟶ FlatSchemeMorphismCat.specObj base //
        hom ≫ targetOver = sourceOver ∧
          AlgebraicGeometry.Flat sourceOver ∧ AlgebraicGeometry.Flat targetOver}

namespace FlatSchemeMorphismCat

variable {Λ k}

/-- The base Artinian local algebra of a flat scheme morphism. -/
abbrev base (P : FlatSchemeMorphismCat Λ k) : ArtinianLocalAlgCat Λ k := P.1

/-- The source scheme of a flat scheme morphism. -/
abbrev source (P : FlatSchemeMorphismCat Λ k) : Scheme.{u} := P.2.1

/-- The target scheme of a flat scheme morphism. -/
abbrev target (P : FlatSchemeMorphismCat Λ k) : Scheme.{u} := P.2.2.1

/-- The underlying scheme morphism of an object. -/
abbrev hom (P : FlatSchemeMorphismCat Λ k) : P.source ⟶ P.target := P.2.2.2.1

/-- The structure map of the source scheme to the base spectrum. -/
abbrev sourceOver (P : FlatSchemeMorphismCat Λ k) : P.source ⟶ specObj P.base :=
  P.2.2.2.2.1

/-- The structure map of the target scheme to the base spectrum. -/
abbrev targetOver (P : FlatSchemeMorphismCat Λ k) : P.target ⟶ specObj P.base :=
  P.2.2.2.2.2.1

/-- The underlying scheme morphism commutes with the structure maps. -/
abbrev isOver (P : FlatSchemeMorphismCat Λ k) : P.hom ≫ P.targetOver = P.sourceOver :=
  P.2.2.2.2.2.2.1

/-- The source structure map of a flat scheme morphism is flat. -/
instance sourceFlat (P : FlatSchemeMorphismCat Λ k) : AlgebraicGeometry.Flat P.sourceOver :=
  P.2.2.2.2.2.2.2.1

/-- The target structure map of a flat scheme morphism is flat. -/
instance targetFlat (P : FlatSchemeMorphismCat Λ k) : AlgebraicGeometry.Flat P.targetOver :=
  P.2.2.2.2.2.2.2.2

/-- Bundle a scheme morphism over an Artinian local algebra with flat structure maps. -/
def of (A : ArtinianLocalAlgCat Λ k) (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (sourceOver : X ⟶ specObj A) (targetOver : Y ⟶ specObj A)
    (isOver : schemeMap ≫ targetOver = sourceOver)
    [sourceFlat : AlgebraicGeometry.Flat sourceOver]
    [targetFlat : AlgebraicGeometry.Flat targetOver] : FlatSchemeMorphismCat Λ k :=
  ⟨A, X, Y, schemeMap, sourceOver, targetOver, isOver, sourceFlat, targetFlat⟩

/-- A flat scheme morphism commutes with its structure maps and has flat source and target. -/
theorem spec (P : FlatSchemeMorphismCat Λ k) :
    P.hom ≫ P.targetOver = P.sourceOver ∧
      AlgebraicGeometry.Flat P.sourceOver ∧ AlgebraicGeometry.Flat P.targetOver := sorry

/-- A base algebra map and reversed scheme maps forming two cartesian squares. -/
def Hom (src tgt : FlatSchemeMorphismCat Λ k) :=
  Σ base : src.base ⟶ tgt.base, Σ sourceMap : tgt.source ⟶ src.source,
    {targetMap : tgt.target ⟶ src.target //
      IsPullback sourceMap tgt.hom src.hom targetMap ∧
        IsPullback targetMap tgt.targetOver src.targetOver (specMap base)}

namespace Hom

/-- The algebra map underlying a cartesian morphism of scheme morphisms. -/
abbrev base {src tgt : FlatSchemeMorphismCat Λ k} (map : Hom src tgt) :
    src.base ⟶ tgt.base := map.1

/-- The reversed map between the source schemes of a cartesian morphism. -/
abbrev sourceMap {src tgt : FlatSchemeMorphismCat Λ k} (map : Hom src tgt) :
    tgt.source ⟶ src.source := map.2.1

/-- The reversed map between the target schemes of a cartesian morphism. -/
abbrev targetMap {src tgt : FlatSchemeMorphismCat Λ k} (map : Hom src tgt) :
    tgt.target ⟶ src.target := map.2.2.1

/-- The square of underlying scheme morphisms is cartesian. -/
abbrev isPullback_top {src tgt : FlatSchemeMorphismCat Λ k} (map : Hom src tgt) :
    IsPullback map.sourceMap tgt.hom src.hom map.targetMap := map.2.2.2.1

/-- The square of target structure maps and base spectra is cartesian. -/
abbrev isPullback_bot {src tgt : FlatSchemeMorphismCat Λ k} (map : Hom src tgt) :
    IsPullback map.targetMap tgt.targetOver src.targetOver (specMap map.base) := map.2.2.2.2

/-- Bundle a base algebra map and reversed scheme maps with cartesian-square witnesses. -/
def of {src tgt : FlatSchemeMorphismCat Λ k} (base : src.base ⟶ tgt.base)
    (sourceMap : tgt.source ⟶ src.source) (targetMap : tgt.target ⟶ src.target)
    (isPullback_top : IsPullback sourceMap tgt.hom src.hom targetMap)
    (isPullback_bot : IsPullback targetMap tgt.targetOver src.targetOver (specMap base)) :
    Hom src tgt :=
  ⟨base, sourceMap, targetMap, isPullback_top, isPullback_bot⟩

/-- Identity maps form cartesian squares for a scheme morphism and its target structure map. -/
theorem id_isPullback (P : FlatSchemeMorphismCat Λ k) :
    IsPullback (𝟙 P.source) P.hom P.hom (𝟙 P.target) ∧
      IsPullback (𝟙 P.target) P.targetOver P.targetOver (specMap (𝟙 P.base)) := sorry

/-- Composing two cartesian morphisms yields two cartesian squares. -/
theorem comp_isPullback {src mid tgt : FlatSchemeMorphismCat Λ k}
    (map : Hom src mid) (nextMap : Hom mid tgt) :
    IsPullback (nextMap.sourceMap ≫ map.sourceMap) tgt.hom src.hom
        (nextMap.targetMap ≫ map.targetMap) ∧
      IsPullback (nextMap.targetMap ≫ map.targetMap) tgt.targetOver src.targetOver
        (specMap (map.base ≫ nextMap.base)) := sorry

/-- The identity cartesian morphism uses identity algebra and scheme maps. -/
def id (P : FlatSchemeMorphismCat Λ k) : Hom P P :=
  of (𝟙 P.base) (𝟙 P.source) (𝟙 P.target) (id_isPullback P).1 (id_isPullback P).2

/-- Composition composes base algebra maps covariantly and scheme maps contravariantly. -/
def comp {src mid tgt : FlatSchemeMorphismCat Λ k} (map : Hom src mid)
    (nextMap : Hom mid tgt) : Hom src tgt :=
  of (map.base ≫ nextMap.base) (nextMap.sourceMap ≫ map.sourceMap)
    (nextMap.targetMap ≫ map.targetMap)
    (comp_isPullback map nextMap).1 (comp_isPullback map nextMap).2

/-- Both squares of a cartesian morphism of scheme morphisms are pullbacks. -/
theorem spec {src tgt : FlatSchemeMorphismCat Λ k} (map : Hom src tgt) :
    IsPullback map.sourceMap tgt.hom src.hom map.targetMap ∧
      IsPullback map.targetMap tgt.targetOver src.targetOver (specMap map.base) := sorry

/-- The base map of an identity cartesian morphism is the identity. -/
theorem id_base (P : FlatSchemeMorphismCat Λ k) : (id P).base = 𝟙 P.base := sorry

/-- The base map of a composite is the composite of the base maps. -/
theorem comp_base {src mid tgt : FlatSchemeMorphismCat Λ k} (map : Hom src mid)
    (nextMap : Hom mid tgt) : (comp map nextMap).base = map.base ≫ nextMap.base := sorry

/-- Composing an identity on the left leaves a cartesian morphism unchanged. -/
theorem id_comp {src tgt : FlatSchemeMorphismCat Λ k} (map : Hom src tgt) :
    comp (id src) map = map := sorry

/-- Composing an identity on the right leaves a cartesian morphism unchanged. -/
theorem comp_id {src tgt : FlatSchemeMorphismCat Λ k} (map : Hom src tgt) :
    comp map (id tgt) = map := sorry

/-- Composition of cartesian morphisms is associative. -/
theorem assoc {src mid next tgt : FlatSchemeMorphismCat Λ k}
    (map : Hom src mid) (nextMap : Hom mid next) (lastMap : Hom next tgt) :
    comp (comp map nextMap) lastMap = comp map (comp nextMap lastMap) := sorry

end Hom

/-- Flat scheme morphisms form a category under cartesian morphisms. -/
instance category : Category.{u} (FlatSchemeMorphismCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

section Forget

variable (Λ k)

/-- The projection sends a flat scheme morphism and a cartesian morphism to their base data. -/
def forget : FlatSchemeMorphismCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj P := P.base
  map := Hom.base
  map_id := Hom.id_base
  map_comp := Hom.comp_base

/-- The object projection recovers the stored Artinian local algebra. -/
theorem forget_obj (P : FlatSchemeMorphismCat Λ k) : (forget Λ k).obj P = P.base := sorry

/-- The morphism projection recovers the stored base algebra map. -/
theorem forget_map {src tgt : FlatSchemeMorphismCat Λ k} (map : src ⟶ tgt) :
    (forget Λ k).map map = map.base := sorry

/-- The projection of flat scheme morphisms to Artinian local algebras is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget : IsFibered.InGroupoids (forget Λ k).op := sorry

/-- A scheme morphism over the residue field defines an object over the residue algebra. -/
def ofResidue (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : schemeMap ≫ hY = hX) : FlatSchemeMorphismCat Λ k :=
  of (ArtinianLocalAlgCat.residue Λ k) X Y schemeMap hX hY hf
    (sourceFlat := flat_over_field hX) (targetFlat := flat_over_field hY)

/-- The base of the residue object is the residue algebra. -/
theorem ofResidue_base (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : schemeMap ≫ hY = hX) :
    (ofResidue Λ k X Y schemeMap hX hY hf).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- A scheme morphism over the residue field, regarded as an object of the residue fibre. -/
def residueObj (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : schemeMap ≫ hY = hX) :
    (forget Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk (rfl : (forget Λ k).obj (ofResidue Λ k X Y schemeMap hX hY hf) =
    ArtinianLocalAlgCat.residue Λ k)

/-- Including the residue-fibre object recovers the concrete scheme morphism over the residue algebra. -/
theorem residueObj_fiberInclusion (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : schemeMap ≫ hY = hX) :
    Fiber.fiberInclusion.obj (residueObj Λ k X Y schemeMap hX hY hf) =
      ofResidue Λ k X Y schemeMap hX hY hf := sorry

/-- The deformation category of a scheme morphism is the slice over its residue object. -/
abbrev deformation (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : schemeMap ≫ hY = hX) :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ k X Y schemeMap hX hY hf))

/-- The deformation category is the over category of the included residue-fibre object. -/
theorem deformation_spec (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : schemeMap ≫ hY = hX) :
    deformation Λ k X Y schemeMap hX hY hf =
      Over (Fiber.fiberInclusion.obj (residueObj Λ k X Y schemeMap hX hY hf)) := sorry

/-- The projection of the residue-object slice is a predeformation category. -/
instance instIsPredeformationCategory_deformation
    (X Y : Scheme.{u}) (schemeMap : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : schemeMap ≫ hY = hX) :
    IsPredeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y schemeMap hX hY hf)) ⋙
        forget Λ k) :=
  instIsPredeformationCategory_overForget (forget Λ k)
    (residueObj Λ k X Y schemeMap hX hY hf)

end Forget

end FlatSchemeMorphismCat
