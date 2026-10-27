/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Complexes.Groupoids
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Scheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass

/-!
# Residue lifts and deformation spaces of relatively perfect complexes

Residue lifts of a complex over Artinian local algebras form a bundled
category. Its projection to the Artinian base defines the tangent space and
infinitesimal automorphism space at the residue complex.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver.Predeformation (specOver specOverMap specOver_toResidue)
open ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X B : AlgebraicSpace S}
variable (f : X ⟶ B)
variable [Proper f] [Flat f] [FinitePresentation f]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x0 : (p f).Fiber (Over.mk kToS))

namespace Predeformation

/-- A residue lift consists of an Artinian base and an arrow from the residue
complex to a complex over the spectrum of that base, lying over the residue map. -/
structure Object where
  /-- The Artinian local `Λ`-algebra over which the target lies. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The target complex in the fibre over `specOver base`. -/
  target : (p f).Fiber (specOver openImmersion base)
  /-- The morphism `x0 ⟶ x` in the total category of `p f`. -/
  fromResidue : Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj target
  /-- `fromResidue` lies over `specOver_toResidue base`. -/
  over_fromResidue :
    (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue

/-- Construct a residue lift from its Artinian base, target complex, and arrow
from the residue complex lying over the residue map. -/
def Object.of (base : ArtinianLocalAlgCat Λ k)
    (target : (p f).Fiber (specOver openImmersion base))
    (fromResidue : Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj target)
    (over_fromResidue :
      (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue) :
    Object f openImmersion kToS h_factor x0 where
  base := base
  target := target
  fromResidue := fromResidue
  over_fromResidue := over_fromResidue

/-- A residue lift has target over its stored base and its residue arrow lies
over the canonical residue spectrum map. -/
theorem Object.spec (ξ : Object f openImmersion kToS h_factor x0) :
    (p f).obj (Fiber.fiberInclusion.obj ξ.target) = specOver openImmersion ξ.base ∧
      (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base)
        ξ.fromResidue := sorry

section

variable {f openImmersion kToS h_factor x0}

/-- A morphism of residue lifts consists of an Artinian base map and a reversed
total-category arrow forming a commutative triangle with the residue arrows. -/
structure Hom (ξ η : Object f openImmersion kToS h_factor x0) where
  /-- The underlying morphism of Artinian local `Λ`-algebras. -/
  baseHom : ξ.base ⟶ η.base
  /-- The reversed arrow `η.target ⟶ ξ.target` in the total category of `p f`. -/
  hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target
  /-- `hom` lies over `specOverMap baseHom`. -/
  over_hom : (p f).IsHomLift (specOverMap openImmersion baseHom) hom
  /-- The triangle `ξ.fromResidue = η.fromResidue ≫ hom`. -/
  triangle : ξ.fromResidue = η.fromResidue ≫ hom

/-- Construct a residue-lift morphism from a base map and a reversed
total-category arrow satisfying lift compatibility and the residue triangle. -/
def Hom.of {ξ η : Object f openImmersion kToS h_factor x0} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom : (p f).IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) : Hom ξ η where
  baseHom := baseHom
  hom := hom
  over_hom := over_hom
  triangle := triangle

/-- The identity base map and total-category identity satisfy lift compatibility
and the residue triangle. -/
theorem Hom.id_laws (ξ : Object f openImmersion kToS h_factor x0) :
    (p f).IsHomLift (specOverMap openImmersion (𝟙 ξ.base))
      (𝟙 (Fiber.fiberInclusion.obj ξ.target)) ∧
      ξ.fromResidue = ξ.fromResidue ≫ 𝟙 (Fiber.fiberInclusion.obj ξ.target) := sorry

/-- The identity residue-lift morphism has identity base map and identity
reversed total-category arrow. -/
def Hom.id (ξ : Object f openImmersion kToS h_factor x0) : Hom ξ ξ :=
  Hom.of (𝟙 ξ.base) (𝟙 (Fiber.fiberInclusion.obj ξ.target))
    (Hom.id_laws ξ).1 (Hom.id_laws ξ).2

/-- Covariant composition of base maps and reversed composition of total-category
arrows preserve lift compatibility and the residue triangle. -/
theorem Hom.comp_laws {ξ η ζ : Object f openImmersion kToS h_factor x0}
    (α : Hom ξ η) (β : Hom η ζ) :
    (p f).IsHomLift (specOverMap openImmersion (α.baseHom ≫ β.baseHom))
      (β.hom ≫ α.hom) ∧
      ξ.fromResidue = ζ.fromResidue ≫ (β.hom ≫ α.hom) := sorry

/-- Composition of residue-lift morphisms composes base maps covariantly and
reverses the order of total-category composition. -/
def Hom.comp {ξ η ζ : Object f openImmersion kToS h_factor x0}
    (α : Hom ξ η) (β : Hom η ζ) : Hom ξ ζ :=
  Hom.of (α.baseHom ≫ β.baseHom) (β.hom ≫ α.hom)
    (Hom.comp_laws α β).1 (Hom.comp_laws α β).2

/-- A residue-lift morphism lies over its base map and commutes with the arrows
from the residue object. -/
theorem Hom.spec {ξ η : Object f openImmersion kToS h_factor x0} (α : Hom ξ η) :
    (p f).IsHomLift (specOverMap openImmersion α.baseHom) α.hom ∧
      ξ.fromResidue = η.fromResidue ≫ α.hom := sorry

/-- Composing an identity on the left leaves a residue-lift morphism unchanged. -/
theorem Hom.id_comp {ξ η : Object f openImmersion kToS h_factor x0} (α : Hom ξ η) :
    Hom.comp (Hom.id ξ) α = α := sorry

/-- Composing an identity on the right leaves a residue-lift morphism unchanged. -/
theorem Hom.comp_id {ξ η : Object f openImmersion kToS h_factor x0} (α : Hom ξ η) :
    Hom.comp α (Hom.id η) = α := sorry

/-- Composition of residue-lift morphisms is associative. -/
theorem Hom.assoc {ξ η ζ ω : Object f openImmersion kToS h_factor x0}
    (α : Hom ξ η) (β : Hom η ζ) (γ : Hom ζ ω) :
    Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ) := sorry

/-- The base map of an identity residue-lift morphism is the identity. -/
theorem baseHom_id (ξ : Object f openImmersion kToS h_factor x0) :
    (Hom.id ξ).baseHom = 𝟙 ξ.base := sorry

/-- The base map of a composite residue-lift morphism is the composite of its
base maps. -/
theorem baseHom_comp {ξ η ζ : Object f openImmersion kToS h_factor x0}
    (α : Hom ξ η) (β : Hom η ζ) :
    (Hom.comp α β).baseHom = α.baseHom ≫ β.baseHom := sorry

end

/-- The bundled category of residue lifts of a complex over Artinian local
`Λ`-algebras, with compatible reversed triangles as morphisms. -/
def category : Cat.{u + 1, u + 1} :=
  ⟨Object f openImmersion kToS h_factor x0, {
    Hom := Hom
    id := Hom.id
    comp := fun α β ↦ Hom.comp α β
    id_comp := Hom.id_comp
    comp_id := Hom.comp_id
    assoc := Hom.assoc
  }⟩

end Predeformation

/-- The projection from the bundled category of residue lifts to their Artinian
local bases, acting on morphisms by the stored base homomorphisms. -/
def predeformationFunctor :
    Predeformation.category f openImmersion kToS h_factor x0 ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := Predeformation.Object.base ξ
  map α := Predeformation.Hom.baseHom α
  map_id := Predeformation.baseHom_id
  map_comp := fun α β ↦ Predeformation.baseHom_comp α β

/-- The predeformation projection sends a residue lift to its stored Artinian base. -/
theorem predeformationFunctor_obj
    (ξ : Predeformation.category f openImmersion kToS h_factor x0) :
    (predeformationFunctor f openImmersion kToS h_factor x0).obj ξ =
      Predeformation.Object.base ξ := sorry

/-- The predeformation projection sends a compatible reversed triangle to its
stored base homomorphism. -/
theorem predeformationFunctor_map
    {ξ η : Predeformation.category f openImmersion kToS h_factor x0} (α : ξ ⟶ η) :
    (predeformationFunctor f openImmersion kToS h_factor x0).map α =
      Predeformation.Hom.baseHom α := sorry

/-- Residue lifts of a relatively perfect complex with vanishing negative fibre
self-Ext along a proper, flat morphism of finite presentation form a deformation
category. -/
instance instIsDeformationCategory_predeformationFunctor :
    Functor.IsDeformationCategory
      (predeformationFunctor f openImmersion kToS h_factor x0) := sorry

/-- The Artin tangent space `Tℱ_{X, k, x0}` is the type of isomorphism classes of
the dual-number fibre of `predeformationFunctor`. -/
abbrev tangentSpace :=
  (Functor.fiberIsoClassFunctor (predeformationFunctor f openImmersion kToS h_factor x0)).obj
    (dualNumber Λ k)

/-- `tangentSpace` is the type of isomorphism classes of the fibre over `k[ε]`. -/
theorem tangentSpace_def :
    tangentSpace f openImmersion kToS h_factor x0 =
      (Functor.fiberIsoClassFunctor (predeformationFunctor f openImmersion kToS h_factor x0)).obj
        (dualNumber Λ k) := sorry

/-- The infinitesimal automorphism space `Inf(ℱ_{X, k, x0})` of the predeformation
functor of `Complexes f` at `x0`. -/
abbrev infinitesimalAutomorphisms :=
  Functor.infinitesimalAutomorphisms
    (predeformationFunctor f openImmersion kToS h_factor x0)

/-- `infinitesimalAutomorphisms` is `Functor.infinitesimalAutomorphisms` of the
associated predeformation functor. -/
theorem infinitesimalAutomorphisms_def :
    infinitesimalAutomorphisms f openImmersion kToS h_factor x0 =
      Functor.infinitesimalAutomorphisms
        (predeformationFunctor f openImmersion kToS h_factor x0) := sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
