/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap98.«98_3_0_2_SpecOver»
public import stacks_project.Chap99.Lemma_99_13_1

/-!
# Predeformation functor of `Spaces'_{fp, flat, proper}`

The Hom-universe of `FpFlatProperGroupoids S` is `u + 1`, so
`FpFlatProperGroupoids.toGroupoids` cannot inhabit `GroupoidsOver S` and cannot
be passed to `GroupoidsOver.Predeformation.predeformationFunctor`. This module
supplies the same 98.3 forgetful functor `ℱ_{𝒳, k, x} ⥤ ArtinianLocalAlgCat Λ k`
directly from `pFpFlatProperGroupoids`, at Hom-universe `u + 1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.GroupoidsOver.Predeformation (specOver specOverMap specOver_toResidue)
open ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace FpFlatProperGroupoids

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
  [AlgebraicGeometry.IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S)
  [AlgebraicGeometry.LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x : (pFpFlatProperGroupoids S).Fiber (Over.mk kToS))

namespace Predeformation

/-- An object of `ℱ_{Spaces'_{fp, flat, proper}, k, x}`: a morphism `x ⟶ ξ` in
`FpFlatProperGroupoids S` lying over `Spec(k) ⟶ Spec(A)` for some
`A : ArtinianLocalAlgCat Λ k`. -/
structure Obj where
  /-- The Artinian local `Λ`-algebra over which the target lies. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The target object of `pFpFlatProperGroupoids S`, lying over `specOver base`. -/
  target : (pFpFlatProperGroupoids S).Fiber (specOver openImmersion base)
  /-- The morphism `x ⟶ target` in the total category of `pFpFlatProperGroupoids S`. -/
  fromResidue :
    Fiber.fiberInclusion.obj x ⟶ Fiber.fiberInclusion.obj target
  /-- `fromResidue` lies over `specOver_toResidue base`. -/
  over_fromResidue :
    (pFpFlatProperGroupoids S).IsHomLift
      (specOver_toResidue openImmersion kToS h_factor base) fromResidue

/-- Bundle an Artinian base, a fibre object, and a lift of `x` into an object of
`ℱ_{Spaces'_{fp, flat, proper}, k, x}`. -/
def Obj.of (base : ArtinianLocalAlgCat Λ k)
    (target : (pFpFlatProperGroupoids S).Fiber (specOver openImmersion base))
    (fromResidue :
      Fiber.fiberInclusion.obj x ⟶ Fiber.fiberInclusion.obj target)
    (over_fromResidue :
      (pFpFlatProperGroupoids S).IsHomLift
        (specOver_toResidue openImmersion kToS h_factor base) fromResidue) :
    Obj openImmersion kToS h_factor x where
  base := base
  target := target
  fromResidue := fromResidue
  over_fromResidue := over_fromResidue

/-- An object of `ℱ_{Spaces'_{fp, flat, proper}, k, x}` is a morphism `x ⟶ ξ`
lying over `specOver_toResidue`. -/
theorem Obj.spec (ξ : Obj openImmersion kToS h_factor x) :
    (pFpFlatProperGroupoids S).obj (Fiber.fiberInclusion.obj ξ.target) =
        specOver openImmersion ξ.base ∧
      (pFpFlatProperGroupoids S).IsHomLift
        (specOver_toResidue openImmersion kToS h_factor ξ.base) ξ.fromResidue :=
  sorry

section

variable {openImmersion kToS h_factor x}

/-- A morphism `(x ⟶ ξ) ⟶ (x ⟶ η)` in `ℱ_{Spaces'_{fp, flat, proper}, k, x}` is a
commutative triangle with reversed arrow `η.target ⟶ ξ.target`. -/
structure Hom (ξ η : Obj openImmersion kToS h_factor x) where
  /-- The underlying morphism of Artinian local `Λ`-algebras. -/
  baseHom : ξ.base ⟶ η.base
  /-- The reversed arrow `η.target ⟶ ξ.target` in the total category. -/
  hom :
    Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target
  /-- `hom` lies over `specOverMap baseHom`. -/
  over_hom :
    (pFpFlatProperGroupoids S).IsHomLift (specOverMap openImmersion baseHom) hom
  /-- The triangle `ξ.fromResidue = η.fromResidue ≫ hom`. -/
  triangle : ξ.fromResidue = η.fromResidue ≫ hom

/-- Bundle a base morphism and a reversed total-category arrow into a morphism of
`ℱ_{Spaces'_{fp, flat, proper}, k, x}`. -/
def Hom.of {ξ η : Obj openImmersion kToS h_factor x} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom :
      (pFpFlatProperGroupoids S).IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) : Hom ξ η where
  baseHom := baseHom
  hom := hom
  over_hom := over_hom
  triangle := triangle

/-- The identity morphism of an object of `ℱ_{Spaces'_{fp, flat, proper}, k, x}`. -/
def Hom.id (ξ : Obj openImmersion kToS h_factor x) : Hom ξ ξ where
  baseHom := 𝟙 ξ.base
  hom := 𝟙 (Fiber.fiberInclusion.obj ξ.target)
  over_hom := sorry
  triangle := sorry

/-- Composition of morphisms of `ℱ_{Spaces'_{fp, flat, proper}, k, x}` composes
base maps covariantly and total-category arrows in reverse. -/
def Hom.comp {ξ η ζ : Obj openImmersion kToS h_factor x} (α : Hom ξ η)
    (β : Hom η ζ) : Hom ξ ζ where
  baseHom := α.baseHom ≫ β.baseHom
  hom := β.hom ≫ α.hom
  over_hom := sorry
  triangle := sorry

/-- A morphism of `ℱ_{Spaces'_{fp, flat, proper}, k, x}` is a base map together
with a reversed triangle in `FpFlatProperGroupoids S`. -/
theorem Hom.spec {ξ η : Obj openImmersion kToS h_factor x} (α : Hom ξ η) :
    (pFpFlatProperGroupoids S).IsHomLift (specOverMap openImmersion α.baseHom)
        α.hom ∧
      ξ.fromResidue = η.fromResidue ≫ α.hom :=
  sorry

end

/-- The category `ℱ_{Spaces'_{fp, flat, proper}, k, x}` of morphisms `x ⟶ ξ`
over Artinian local `Λ`-algebras. Hom-types of `FpFlatProperGroupoids S` live in
`Type (u + 1)`. -/
instance category : Category.{u + 1} (Obj openImmersion kToS h_factor x) where
  Hom := Hom
  id := Hom.id
  comp α β := Hom.comp α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The forgetful functor `ℱ_{Spaces'_{fp, flat, proper}, k, x} ⥤
ArtinianLocalAlgCat Λ k`. -/
def forget : Obj openImmersion kToS h_factor x ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map α := α.baseHom
  map_id := sorry
  map_comp := sorry

/-- The object map of `forget` is the stored Artinian base. -/
theorem forget_obj (ξ : Obj openImmersion kToS h_factor x) :
    (forget openImmersion kToS h_factor x).obj ξ = ξ.base :=
  sorry

/-- The morphism map of `forget` is the stored base homomorphism. -/
theorem forget_map {ξ η : Obj openImmersion kToS h_factor x} (α : ξ ⟶ η) :
    (forget openImmersion kToS h_factor x).map α = α.baseHom :=
  sorry

end Predeformation

/-- The predeformation functor associated to a residue object of
`pFpFlatProperGroupoids S`, sending a morphism `x ⟶ ξ` over `Spec(A)` to the
Artinian local `Λ`-algebra `A`. -/
def predeformationFunctor :
    Predeformation.Obj openImmersion kToS h_factor x ⥤ ArtinianLocalAlgCat Λ k :=
  Predeformation.forget openImmersion kToS h_factor x

/-- The labeled functor sends an object `x ⟶ ξ` over `Spec(A)` to `A`. -/
theorem predeformationFunctor_obj
    (ξ : Predeformation.Obj openImmersion kToS h_factor x) :
    (predeformationFunctor openImmersion kToS h_factor x).obj ξ = ξ.base :=
  sorry

/-- The opposite of `predeformationFunctor` is cofibered in groupoids. -/
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
  sorry

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
  sorry

end FpFlatProperGroupoids
end AlgebraicGeometry.AlgebraicSpace.Spaces
