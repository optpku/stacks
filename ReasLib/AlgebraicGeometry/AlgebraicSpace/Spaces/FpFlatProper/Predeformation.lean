/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Groupoids
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Spaces.Pushout
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Predeformation
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Scheme

/-!
# Predeformations of finite-presentation, flat, proper algebraic spaces

Residue lifts over Artinian local algebras form a category whose projection
is a deformation category. Its dual-number fibre and infinitesimal
automorphisms give the Artin deformation spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids

open AlgebraicGeometry.GroupoidsOver.Predeformation (specOver specOverMap specOver_toResidue)
open ArtinianLocalAlgCat

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS))

namespace Predeformation

/-- An object of `ℱ_{𝒳, k, x₀}`: a morphism `x₀ ⟶ x` in `𝒳` lying over
`Spec(k) ⟶ Spec(A)` for some `A : ArtinianLocalAlgCat Λ k`. -/
structure Object where
  /-- The Artinian local `Λ`-algebra over which the target lies. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The target object `x` of `𝒳`, lying over `specOver base`. -/
  target : (pFpFlatProperGroupoids S).Fiber (specOver openImmersion base)
  /-- The morphism `x₀ ⟶ x` in the total category of `𝒳`. -/
  fromResidue : Fiber.fiberInclusion.obj x ⟶ Fiber.fiberInclusion.obj target
  /-- `fromResidue` lies over `specOver_toResidue base`. -/
  over_fromResidue :
    (pFpFlatProperGroupoids S).IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue

/-- Construct an Artinian base, a fiber object, and a residue lift as explicit object data. -/
def Object.of (base : ArtinianLocalAlgCat Λ k)
    (target : (pFpFlatProperGroupoids S).Fiber (specOver openImmersion base))
    (fromResidue : Fiber.fiberInclusion.obj x ⟶ Fiber.fiberInclusion.obj target)
    (over_fromResidue :
      (pFpFlatProperGroupoids S).IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue) :
    Object openImmersion kToS h_factor x where
  base := base
  target := target
  fromResidue := fromResidue
  over_fromResidue := over_fromResidue

section

variable {openImmersion kToS h_factor x}

/-- A morphism `(x₀ ⟶ x) ⟶ (x₀ ⟶ x')` in `ℱ_{𝒳, k, x₀}` is a commutative
triangle with reversed arrow `x' ⟶ x` in `𝒳`. -/
structure Arrow (ξ η : Object openImmersion kToS h_factor x) where
  /-- The underlying morphism of Artinian local `Λ`-algebras. -/
  baseHom : ξ.base ⟶ η.base
  /-- The reversed arrow `η.target ⟶ ξ.target` in the total category of `𝒳`. -/
  hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target
  /-- `hom` lies over `specOverMap baseHom`. -/
  over_hom : (pFpFlatProperGroupoids S).IsHomLift (specOverMap openImmersion baseHom) hom
  /-- The triangle `ξ.fromResidue = η.fromResidue ≫ hom`. -/
  triangle : ξ.fromResidue = η.fromResidue ≫ hom

/-- Construct explicit morphism data from a base map and a compatible reversed triangle. -/
def Arrow.of {ξ η : Object openImmersion kToS h_factor x} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom : (pFpFlatProperGroupoids S).IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) : Arrow ξ η where
  baseHom := baseHom
  hom := hom
  over_hom := over_hom
  triangle := triangle

/-- The categorical morphisms of predeformations are compatible reversed triangles. -/
def Hom (ξ η : Object openImmersion kToS h_factor x) := Arrow ξ η

/-- The map of Artinian local bases underlying a predeformation morphism. -/
def Hom.baseHom {ξ η : Object openImmersion kToS h_factor x} (morphism : Hom ξ η) :
    ξ.base ⟶ η.base :=
  Arrow.baseHom morphism

/-- The reversed arrow in the total category underlying a predeformation morphism. -/
def Hom.hom {ξ η : Object openImmersion kToS h_factor x} (morphism : Hom ξ η) :
    Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target :=
  Arrow.hom morphism

/-- The reversed arrow of a predeformation morphism lies over its spectrum map. -/
abbrev Hom.over_hom {ξ η : Object openImmersion kToS h_factor x} (morphism : Hom ξ η) :
    (pFpFlatProperGroupoids S).IsHomLift (specOverMap openImmersion morphism.baseHom) morphism.hom :=
  Arrow.over_hom morphism

/-- The reversed arrow of a predeformation morphism commutes with the residue arrows. -/
abbrev Hom.triangle {ξ η : Object openImmersion kToS h_factor x} (morphism : Hom ξ η) :
    ξ.fromResidue = η.fromResidue ≫ morphism.hom :=
  Arrow.triangle morphism

/-- Bundle a base map and a compatible reversed triangle as a predeformation morphism. -/
def Hom.of {ξ η : Object openImmersion kToS h_factor x} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom : (pFpFlatProperGroupoids S).IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) : Hom ξ η :=
  Arrow.of baseHom hom over_hom triangle

/-- The identity morphism of an object of `ℱ_{𝒳, k, x₀}`. -/
def Hom.id (ξ : Object openImmersion kToS h_factor x) : Hom ξ ξ := by
  have laws :
      (pFpFlatProperGroupoids S).IsHomLift
        (specOverMap openImmersion (𝟙 ξ.base))
        (𝟙 (Fiber.fiberInclusion.obj ξ.target)) ∧
      ξ.fromResidue = ξ.fromResidue ≫ 𝟙 (Fiber.fiberInclusion.obj ξ.target) := by
    sorry
  exact Hom.of (𝟙 ξ.base) (𝟙 (Fiber.fiberInclusion.obj ξ.target)) laws.1 laws.2

/-- Composition of morphisms of `ℱ_{𝒳, k, x₀}` composes base maps covariantly and
total-category arrows in reverse. -/
def Hom.comp {ξ η ζ : Object openImmersion kToS h_factor x} (f : Hom ξ η) (g : Hom η ζ) :
    Hom ξ ζ := by
  have laws :
      (pFpFlatProperGroupoids S).IsHomLift
        (specOverMap openImmersion (f.baseHom ≫ g.baseHom)) (g.hom ≫ f.hom) ∧
      ξ.fromResidue = ζ.fromResidue ≫ (g.hom ≫ f.hom) := by
    sorry
  exact Hom.of (f.baseHom ≫ g.baseHom) (g.hom ≫ f.hom) laws.1 laws.2

/-- A morphism of `ℱ_{𝒳, k, x₀}` is a base map together with a reversed triangle
in `𝒳`. -/
theorem Hom.spec {ξ η : Object openImmersion kToS h_factor x} (f : Hom ξ η) :
    (pFpFlatProperGroupoids S).IsHomLift (specOverMap openImmersion f.baseHom) f.hom ∧
      ξ.fromResidue = η.fromResidue ≫ f.hom :=
  ⟨f.over_hom, f.triangle⟩

end

/-- The category `ℱ_{𝒳, k, x₀}` of morphisms `x₀ ⟶ x` over Artinian local
`Λ`-algebras. -/
def category : Cat.{u + 1, u + 1} := by
  have laws :
      (∀ {ξ η : Object openImmersion kToS h_factor x} (f : Hom ξ η),
        Hom.comp (Hom.id ξ) f = f) ∧
      (∀ {ξ η : Object openImmersion kToS h_factor x} (f : Hom ξ η),
        Hom.comp f (Hom.id η) = f) ∧
      (∀ {ξ η ζ ω : Object openImmersion kToS h_factor x}
        (f : Hom ξ η) (g : Hom η ζ) (h : Hom ζ ω),
        Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h)) := by
    sorry
  exact ⟨Object openImmersion kToS h_factor x, {
    Hom := Hom
    id := Hom.id
    comp := Hom.comp
    id_comp := laws.1
    comp_id := laws.2.1
    assoc := laws.2.2 }⟩

/-- The categorical carrier of residue lifts over Artinian local algebras. -/
abbrev Obj : Type (u + 1) := category openImmersion kToS h_factor x

section

variable {openImmersion kToS h_factor x}

/-- The Artinian local base of a predeformation object. -/
def Obj.base (ξ : Obj openImmersion kToS h_factor x) : ArtinianLocalAlgCat Λ k :=
  Object.base ξ

/-- The target in the fiber over the spectrum of a predeformation's base. -/
def Obj.target (ξ : Obj openImmersion kToS h_factor x) :
    (pFpFlatProperGroupoids S).Fiber (specOver openImmersion ξ.base) :=
  Object.target ξ

/-- The arrow from the chosen residue object to the target of a predeformation. -/
def Obj.fromResidue (ξ : Obj openImmersion kToS h_factor x) :
    Fiber.fiberInclusion.obj x ⟶ Fiber.fiberInclusion.obj ξ.target :=
  Object.fromResidue ξ

/-- The residue arrow of a predeformation lies over its residue spectrum map. -/
abbrev Obj.over_fromResidue (ξ : Obj openImmersion kToS h_factor x) :
    (pFpFlatProperGroupoids S).IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base) ξ.fromResidue :=
  Object.over_fromResidue ξ

end

/-- Bundle an Artinian base, a fiber object, and a residue lift as a predeformation. -/
def Obj.of (base : ArtinianLocalAlgCat Λ k)
    (target : (pFpFlatProperGroupoids S).Fiber (specOver openImmersion base))
    (fromResidue : Fiber.fiberInclusion.obj x ⟶ Fiber.fiberInclusion.obj target)
    (over_fromResidue :
      (pFpFlatProperGroupoids S).IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue) :
    Obj openImmersion kToS h_factor x :=
  Object.of openImmersion kToS h_factor x base target fromResidue over_fromResidue

/-- An object of `ℱ_{𝒳, k, x₀}` is a morphism `x₀ ⟶ x` lying over
`specOver_toResidue`. -/
theorem Obj.spec (ξ : Obj openImmersion kToS h_factor x) :
    (pFpFlatProperGroupoids S).obj (Fiber.fiberInclusion.obj ξ.target) = specOver openImmersion ξ.base ∧
      (pFpFlatProperGroupoids S).IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base)
        ξ.fromResidue :=
  ⟨ξ.target.property, ξ.over_fromResidue⟩

/-- The forgetful functor `p : ℱ_{𝒳, k, x₀} ⥤ ArtinianLocalAlgCat Λ k`. -/
def forget : Obj openImmersion kToS h_factor x ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map f := f.baseHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The object map of `forget` is the stored Artinian base. -/
theorem forget_obj (ξ : Obj openImmersion kToS h_factor x) :
    (forget openImmersion kToS h_factor x).obj ξ = ξ.base :=
  rfl

/-- The morphism map of `forget` is the stored base homomorphism. -/
theorem forget_map {ξ η : Obj openImmersion kToS h_factor x} (f : ξ ⟶ η) :
    (forget openImmersion kToS h_factor x).map f = f.baseHom :=
  rfl

end Predeformation

/-- The predeformation functor associated to a residue object of
`pFpFlatProperGroupoids S`, sending a morphism `x ⟶ ξ` over `Spec(A)` to the
Artinian local `Λ`-algebra `A`. -/
def predeformationFunctor :
    Predeformation.Obj openImmersion kToS h_factor x ⥤ ArtinianLocalAlgCat Λ k :=
  Predeformation.forget openImmersion kToS h_factor x

/-- The predeformation functor sends an object `x ⟶ ξ` over `Spec(A)` to `A`. -/
theorem predeformationFunctor_obj
    (ξ : Predeformation.Obj openImmersion kToS h_factor x) :
    (predeformationFunctor openImmersion kToS h_factor x).obj ξ = ξ.base :=
  rfl

/-- The predeformation projection is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_predeformationFunctor :
    Functor.IsFibered.InGroupoids
      (predeformationFunctor openImmersion kToS h_factor x).op :=
  sorry

/-- The predeformation functor of `pFpFlatProperGroupoids` at a residue object is
a deformation category. -/
instance instIsDeformationCategory_predeformationFunctor :
    Functor.IsDeformationCategory
      (predeformationFunctor openImmersion kToS h_factor x) :=
  sorry

/-- The Artin tangent space `Tℱ_{𝒳, k, x}` is the type of isomorphism classes of
the dual-number fibre of `predeformationFunctor`. -/
abbrev tangentSpace :=
  (Functor.fiberIsoClassFunctor
      (predeformationFunctor openImmersion kToS h_factor x)).obj
    (dualNumber Λ k)

/-- `tangentSpace` is the type of isomorphism classes of the fibre over `k[ε]`. -/
theorem tangentSpace_def :
    tangentSpace openImmersion kToS h_factor x =
      (Functor.fiberIsoClassFunctor
          (predeformationFunctor openImmersion kToS h_factor x)).obj
        (dualNumber Λ k) :=
  rfl

/-- The infinitesimal automorphism space `Inf(ℱ_{𝒳, k, x})` of the predeformation
functor of `pFpFlatProperGroupoids` at `x`. -/
abbrev infinitesimalAutomorphisms :=
  Functor.infinitesimalAutomorphisms
    (predeformationFunctor openImmersion kToS h_factor x)

/-- `infinitesimalAutomorphisms` is `Functor.infinitesimalAutomorphisms` of the
associated predeformation functor. -/
theorem infinitesimalAutomorphisms_def :
    infinitesimalAutomorphisms openImmersion kToS h_factor x =
      Functor.infinitesimalAutomorphisms
        (predeformationFunctor openImmersion kToS h_factor x) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace.Spaces.FpFlatProperGroupoids
