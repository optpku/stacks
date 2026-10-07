module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap90.Remark_90_6_4

/-!
# Category of morphisms of schemes flat over objects of `ArtinianLocalAlgCat`

Objects are pairs `(A, X ⟶ Y)` with `A` in `ArtinianLocalAlgCat` and `X ⟶ Y` a
morphism of schemes over `A` with both `X` and `Y` flat over `A`. Morphisms are
triples `(f, g, h)` whose associated Spec-diagram has both squares cartesian.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

universe u

noncomputable section

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace FlatSchemeMorphismCat

variable {Λ k}

/-- The spectrum of the underlying algebra of an object of `C_Λ`. -/
abbrev specObj (A : ArtinianLocalAlgCat Λ k) : Scheme.{u} :=
  Spec (CommRingCat.of A.carrier)

/-- The morphism of spectra associated with a morphism of `C_Λ`. -/
def specMap {A B : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) :
    specObj B ⟶ specObj A :=
  Spec.map (CommRingCat.ofHom f.hom.toRingHom)

/-- `specMap` sends identity morphisms of `C_Λ` to identity morphisms of spectra. -/
theorem specMap_id (A : ArtinianLocalAlgCat Λ k) :
    specMap (𝟙 A) = 𝟙 (specObj A) := sorry

/-- `specMap` is contravariant on morphisms of `C_Λ`. -/
theorem specMap_comp {A B C : ArtinianLocalAlgCat Λ k} (f : A ⟶ B) (g : B ⟶ C) :
    specMap (f ≫ g) = specMap g ≫ specMap f := sorry

end FlatSchemeMorphismCat

/-- An object of the category `F` of pairs `(A, X ⟶ Y)` with `A` in `C_Λ` and
`X ⟶ Y` a morphism of schemes over `A` with both `X` and `Y` flat over `A`. -/
structure FlatSchemeMorphismCat where
  /-- Underlying object of `ArtinianLocalAlgCat Λ k`. -/
  base : ArtinianLocalAlgCat Λ k
  /-- Source scheme of the stored morphism. -/
  source : Scheme.{u}
  /-- Target scheme of the stored morphism. -/
  target : Scheme.{u}
  /-- Underlying morphism of schemes over the base. -/
  hom : source ⟶ target
  /-- Structure morphism exhibiting the source as a scheme over the base. -/
  sourceOver : source ⟶ Spec (CommRingCat.of base.carrier)
  /-- Structure morphism exhibiting the target as a scheme over the base. -/
  targetOver : target ⟶ Spec (CommRingCat.of base.carrier)
  /-- The stored morphism is a morphism of schemes over the base. -/
  isOver : hom ≫ targetOver = sourceOver
  /-- The source is flat over the base. -/
  [sourceFlat : AlgebraicGeometry.Flat sourceOver]
  /-- The target is flat over the base. -/
  [targetFlat : AlgebraicGeometry.Flat targetOver]

attribute [instance] FlatSchemeMorphismCat.sourceFlat FlatSchemeMorphismCat.targetFlat

namespace FlatSchemeMorphismCat

variable {Λ k}

/-- Pair an Artinian local algebra with a morphism of schemes flat over it. -/
def of (A : ArtinianLocalAlgCat Λ k) (X Y : Scheme.{u}) (f : X ⟶ Y)
    (sourceOver : X ⟶ Spec (CommRingCat.of A.carrier))
    (targetOver : Y ⟶ Spec (CommRingCat.of A.carrier))
    (isOver : f ≫ targetOver = sourceOver)
    [sourceFlat : AlgebraicGeometry.Flat sourceOver]
    [targetFlat : AlgebraicGeometry.Flat targetOver] :
    FlatSchemeMorphismCat Λ k where
  base := A
  source := X
  target := Y
  hom := f
  sourceOver := sourceOver
  targetOver := targetOver
  isOver := isOver
  sourceFlat := sourceFlat
  targetFlat := targetFlat

/-- An object of `F` is a morphism of schemes over `A` with both schemes flat over `A`. -/
theorem spec (P : FlatSchemeMorphismCat Λ k) :
    P.hom ≫ P.targetOver = P.sourceOver ∧
      AlgebraicGeometry.Flat P.sourceOver ∧
      AlgebraicGeometry.Flat P.targetOver := sorry

/-- A morphism `(f, g, h) : (A', X' ⟶ Y') ⟶ (A, X ⟶ Y)` is a morphism
`f : A' ⟶ A` in `C_Λ` together with `g : X ⟶ X'` and `h : Y ⟶ Y'` making both
squares of the displayed Spec-diagram cartesian. -/
structure Hom (src tgt : FlatSchemeMorphismCat Λ k) where
  /-- Underlying morphism of Artinian local algebras. -/
  base : src.base ⟶ tgt.base
  /-- Underlying source scheme morphism, pointing toward the source object. -/
  sourceMap : tgt.source ⟶ src.source
  /-- Underlying target scheme morphism, pointing toward the source object. -/
  targetMap : tgt.target ⟶ src.target
  /-- The square of scheme morphisms `X ⟶ X'`, `X ⟶ Y`, `X' ⟶ Y'`, `Y ⟶ Y'` is cartesian. -/
  isPullback_top : IsPullback sourceMap tgt.hom src.hom targetMap
  /-- The square of structure morphisms `Y ⟶ Y'`, `Y ⟶ Spec A`, `Y' ⟶ Spec A'`,
  `Spec A ⟶ Spec A'` is cartesian. -/
  isPullback_bot : IsPullback targetMap tgt.targetOver src.targetOver (specMap base)

namespace Hom

/-- Package a base morphism and opposite scheme morphisms forming two cartesian squares. -/
def of {src tgt : FlatSchemeMorphismCat Λ k} (base : src.base ⟶ tgt.base)
    (sourceMap : tgt.source ⟶ src.source) (targetMap : tgt.target ⟶ src.target)
    (isPullback_top : IsPullback sourceMap tgt.hom src.hom targetMap)
    (isPullback_bot :
      IsPullback targetMap tgt.targetOver src.targetOver (specMap base)) :
    Hom src tgt where
  base := base
  sourceMap := sourceMap
  targetMap := targetMap
  isPullback_top := isPullback_top
  isPullback_bot := isPullback_bot

/-- Identity morphism of a pair `(A, X ⟶ Y)`. -/
def id (P : FlatSchemeMorphismCat Λ k) : Hom P P where
  base := 𝟙 P.base
  sourceMap := 𝟙 P.source
  targetMap := 𝟙 P.target
  isPullback_top := sorry
  isPullback_bot := sorry

/-- Composition of morphisms of pairs. -/
def comp {src mid tgt : FlatSchemeMorphismCat Λ k} (f : Hom src mid) (g : Hom mid tgt) :
    Hom src tgt where
  base := f.base ≫ g.base
  sourceMap := g.sourceMap ≫ f.sourceMap
  targetMap := g.targetMap ≫ f.targetMap
  isPullback_top := sorry
  isPullback_bot := sorry

/-- A morphism is a pair of cartesian squares in the displayed Spec-diagram. -/
theorem spec {src tgt : FlatSchemeMorphismCat Λ k} (f : Hom src tgt) :
    IsPullback f.sourceMap tgt.hom src.hom f.targetMap ∧
      IsPullback f.targetMap tgt.targetOver src.targetOver (specMap f.base) :=
  sorry

/-- The identity morphism has identity base arrow. -/
theorem id_base (P : FlatSchemeMorphismCat Λ k) : (id P).base = 𝟙 P.base := sorry

/-- Composition of morphisms has composed base arrows. -/
theorem comp_base {src mid tgt : FlatSchemeMorphismCat Λ k} (f : Hom src mid)
    (g : Hom mid tgt) : (comp f g).base = f.base ≫ g.base := sorry

end Hom

/-- Category of pairs `(A, X ⟶ Y)` with cartesian Spec-diagrams as morphisms. -/
instance category : Category.{u} (FlatSchemeMorphismCat Λ k) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

section Forget

variable (Λ k)

/-- The functor `p` sending `(A, X ⟶ Y)` to `A` and `(f, g, h)` to `f`. -/
def forget : FlatSchemeMorphismCat Λ k ⥤ ArtinianLocalAlgCat Λ k where
  obj P := P.base
  map f := f.base
  map_id := sorry
  map_comp := sorry

/-- The forgetful functor evaluates to the stored base algebra. -/
theorem forget_obj (P : FlatSchemeMorphismCat Λ k) : (forget Λ k).obj P = P.base := sorry

/-- The forgetful functor sends a morphism to its base arrow. -/
theorem forget_map {src tgt : FlatSchemeMorphismCat Λ k} (f : src ⟶ tgt) :
    (forget Λ k).map f = f.base := sorry

/-- The projection `p : F ⥤ C_Λ` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_forget :
    IsFibered.InGroupoids (forget Λ k).op := sorry

/-- The residue object `x0 = (k, X ⟶ Y)` of a morphism of schemes over `k`. -/
def ofResidue (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [hXflat : AlgebraicGeometry.Flat hX] [hYflat : AlgebraicGeometry.Flat hY] :
    FlatSchemeMorphismCat Λ k where
  base := ArtinianLocalAlgCat.residue Λ k
  source := X
  target := Y
  hom := f
  sourceOver := hX
  targetOver := hY
  isOver := hf
  sourceFlat := hXflat
  targetFlat := hYflat

/-- The forgetful image of `ofResidue X Y f hX hY hf` is the residue object of `C_Λ`. -/
theorem ofResidue_base (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    (ofResidue Λ k X Y f hX hY hf).base = ArtinianLocalAlgCat.residue Λ k := sorry

/-- `x0 = (k, X ⟶ Y)` as an object of the residue fibre of `forget`. -/
def residueObj (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    (forget Λ k).Fiber (ArtinianLocalAlgCat.residue Λ k) :=
  Fiber.mk
    (rfl : (forget Λ k).obj (ofResidue Λ k X Y f hX hY hf) =
      ArtinianLocalAlgCat.residue Λ k)

/-- The residue-fibre object is included as `ofResidue X Y f hX hY hf`. -/
theorem residueObj_fiberInclusion (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf) =
      ofResidue Λ k X Y f hX hY hf := sorry

/-- The deformation category `Def_{X ⟶ Y}` is the slice `F_{x0}` at `x0 = (k, X ⟶ Y)`. -/
abbrev deformation (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :=
  Over (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf))

/-- `deformation` is the Over-slice of the residue-fibre object `x0 = (k, X ⟶ Y)`. -/
theorem deformation_spec (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    deformation Λ k X Y f hX hY hf =
      Over (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) := sorry

/-- The slice projection `p_{x0} : F_{x0} ⥤ C_Λ` is a predeformation category. -/
instance instIsPredeformationCategory_deformation
    (X Y : Scheme.{u}) (f : X ⟶ Y)
    (hX : X ⟶ Spec (CommRingCat.of k)) (hY : Y ⟶ Spec (CommRingCat.of k))
    (hf : f ≫ hY = hX)
    [AlgebraicGeometry.Flat hX] [AlgebraicGeometry.Flat hY] :
    IsPredeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (residueObj Λ k X Y f hX hY hf)) ⋙
        forget Λ k) :=
  inferInstance

end Forget

end FlatSchemeMorphismCat
