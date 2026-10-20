module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap90.Remark_90_19_4_InfinitesimalAut
public import stacks_project.Chap90.Remarks_90_5_2_IsoClass
public import stacks_project.Chap98.«98_3_0_2_SpecOver»
public import stacks_project.Chap99.Lemma_99_16_4

/-!
# Predeformation functor of `Complexes_{X/B}`

The Hom-universe of `Obj f` is `u + 1`, so `toGroupoids f` cannot inhabit
`GroupoidsOver S` and cannot be passed to
`GroupoidsOver.Predeformation.predeformationFunctor`. This module supplies the
same 98.3 forgetful functor `ℱ_{X, k, x0} ⥤ ArtinianLocalAlgCat Λ k` directly
from `p f`, at Hom-universe `u + 1`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.GroupoidsOver.Predeformation (specOver specOverMap specOver_toResidue)
open ArtinianLocalAlgCat

noncomputable section

universe u

attribute [local instance] SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor

namespace AlgebraicGeometry.AlgebraicSpace.Complexes

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {X B : AlgebraicSpace S}
variable (f : X ⟶ B)
variable [chartDerived : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
  (Functor.Homotopy.toDerived (Modules.restrictToScheme sq.left.left)).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (Modules (ofOver sq.left.left)) (ComplexShape.up ℤ))]
variable [chartTensor : ∀ σ : SchemeOver B, ∀ sq : EtaleSquare (Limits.pullback.snd f σ.hom),
  ∀ U : TopologicalSpace.Opens (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).carrier,
  let Z := (RingedSpace.Hom.inverseImageBase sq.map.left.toShHom).restrict U.isOpenEmbedding
  DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Z)]
variable [Proper f] [Flat f] [FinitePresentation f]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x0 : (p f).Fiber (Over.mk kToS))

namespace Predeformation

/-- An object of `ℱ_{Complexes_{X/B}, k, x0}`: a morphism `x0 ⟶ x` in `Obj f`
lying over `Spec(k) ⟶ Spec(A)` for some `A : ArtinianLocalAlgCat Λ k`. -/
structure Obj where
  /-- The Artinian local `Λ`-algebra over which the target lies. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The target object `x` of `Obj f`, lying over `specOver base`. -/
  target : (p f).Fiber (specOver openImmersion base)
  /-- The morphism `x0 ⟶ x` in the total category of `p f`. -/
  fromResidue : Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj target
  /-- `fromResidue` lies over `specOver_toResidue base`. -/
  over_fromResidue :
    (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue

/-- Bundle an Artinian base, a fibre object, and a lift of `x0` into an object of
`ℱ_{Complexes_{X/B}, k, x0}`. -/
def Obj.of (base : ArtinianLocalAlgCat Λ k)
    (target : (p f).Fiber (specOver openImmersion base))
    (fromResidue : Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj target)
    (over_fromResidue :
      (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue) :
    Obj f openImmersion kToS h_factor x0 where
  base := base
  target := target
  fromResidue := fromResidue
  over_fromResidue := over_fromResidue

/-- An object of `ℱ_{Complexes_{X/B}, k, x0}` is a morphism `x0 ⟶ x` lying over
`specOver_toResidue`. -/
theorem Obj.spec (ξ : Obj f openImmersion kToS h_factor x0) :
    (p f).obj (Fiber.fiberInclusion.obj ξ.target) = specOver openImmersion ξ.base ∧
      (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base)
        ξ.fromResidue :=
  sorry

section

variable {f openImmersion kToS h_factor x0}

/-- A morphism `(x0 ⟶ x) ⟶ (x0 ⟶ x')` in `ℱ_{Complexes_{X/B}, k, x0}` is a
commutative triangle with reversed arrow `x' ⟶ x` in `Obj f`. -/
structure Hom (ξ η : Obj f openImmersion kToS h_factor x0) where
  /-- The underlying morphism of Artinian local `Λ`-algebras. -/
  baseHom : ξ.base ⟶ η.base
  /-- The reversed arrow `η.target ⟶ ξ.target` in the total category of `p f`. -/
  hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target
  /-- `hom` lies over `specOverMap baseHom`. -/
  over_hom : (p f).IsHomLift (specOverMap openImmersion baseHom) hom
  /-- The triangle `ξ.fromResidue = η.fromResidue ≫ hom`. -/
  triangle : ξ.fromResidue = η.fromResidue ≫ hom

/-- Bundle a base morphism and a reversed total-category arrow into a morphism of
`ℱ_{Complexes_{X/B}, k, x0}`. -/
def Hom.of {ξ η : Obj f openImmersion kToS h_factor x0} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom : (p f).IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) :
    Hom (f := f) (chartDerived := chartDerived) (chartTensor := chartTensor)
    (openImmersion := openImmersion) (kToS := kToS) (h_factor := h_factor) (x0 := x0) ξ η where
  baseHom := baseHom
  hom := hom
  over_hom := over_hom
  triangle := triangle

/-- The identity morphism of an object of `ℱ_{Complexes_{X/B}, k, x0}`. -/
def Hom.id (ξ : Obj f openImmersion kToS h_factor x0) :
    Hom (f := f) (chartDerived := chartDerived) (chartTensor := chartTensor)
    (openImmersion := openImmersion) (kToS := kToS) (h_factor := h_factor) (x0 := x0) ξ ξ where
  baseHom := 𝟙 ξ.base
  hom := 𝟙 (Fiber.fiberInclusion.obj ξ.target)
  over_hom := sorry
  triangle := sorry

/-- Composition of morphisms of `ℱ_{Complexes_{X/B}, k, x0}` composes base maps
covariantly and total-category arrows in reverse. -/
def Hom.comp {ξ η ζ : Obj f openImmersion kToS h_factor x0} (α : Hom (f := f) (chartDerived := chartDerived) (chartTensor := chartTensor)
    (openImmersion := openImmersion) (kToS := kToS) (h_factor := h_factor) (x0 := x0) ξ η)
    (β : Hom (f := f) (chartDerived := chartDerived) (chartTensor := chartTensor)
    (openImmersion := openImmersion) (kToS := kToS) (h_factor := h_factor) (x0 := x0) η ζ) :
    Hom (f := f) (chartDerived := chartDerived) (chartTensor := chartTensor)
    (openImmersion := openImmersion) (kToS := kToS) (h_factor := h_factor) (x0 := x0) ξ ζ where
  baseHom := α.baseHom ≫ β.baseHom
  hom := β.hom ≫ α.hom
  over_hom := sorry
  triangle := sorry

/-- A morphism of `ℱ_{Complexes_{X/B}, k, x0}` is a base map together with a
reversed triangle in `Obj f`. -/
theorem Hom.spec {ξ η : Obj f openImmersion kToS h_factor x0} (α : Hom (f := f) (chartDerived := chartDerived) (chartTensor := chartTensor)
    (openImmersion := openImmersion) (kToS := kToS) (h_factor := h_factor) (x0 := x0) ξ η) :
    (p f).IsHomLift (specOverMap openImmersion α.baseHom) α.hom ∧
      ξ.fromResidue = η.fromResidue ≫ α.hom :=
  sorry

end

/-- The category `ℱ_{Complexes_{X/B}, k, x0}` of morphisms `x0 ⟶ x` over
Artinian local `Λ`-algebras. Hom-types of `Obj f` live in `Type (u + 1)`. -/
instance category : Category.{u + 1} (Obj f openImmersion kToS h_factor x0) where
  Hom := Hom (f := f) (chartDerived := chartDerived) (chartTensor := chartTensor)
    (openImmersion := openImmersion) (kToS := kToS) (h_factor := h_factor) (x0 := x0)
  id := Hom.id (f := f) (chartDerived := chartDerived) (chartTensor := chartTensor)
    (openImmersion := openImmersion) (kToS := kToS) (h_factor := h_factor) (x0 := x0)
  comp α β := Hom.comp (f := f) (chartDerived := chartDerived) (chartTensor := chartTensor)
    (openImmersion := openImmersion) (kToS := kToS) (h_factor := h_factor) (x0 := x0) α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The forgetful functor `p : ℱ_{Complexes_{X/B}, k, x0} ⥤ ArtinianLocalAlgCat Λ k`. -/
def forget : Obj f openImmersion kToS h_factor x0 ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map α := α.baseHom
  map_id := sorry
  map_comp := sorry

/-- The object map of `forget` is the stored Artinian base. -/
theorem forget_obj (ξ : Obj f openImmersion kToS h_factor x0) :
    (forget f openImmersion kToS h_factor x0).obj ξ = ξ.base :=
  sorry

/-- The morphism map of `forget` is the stored base homomorphism. -/
theorem forget_map {ξ η : Obj f openImmersion kToS h_factor x0} (α : ξ ⟶ η) :
    (forget f openImmersion kToS h_factor x0).map α = α.baseHom :=
  sorry

end Predeformation

/-- The predeformation functor associated to a residue object of `Complexes f`,
sending a morphism `x0 ⟶ x` over `Spec(A)` to the Artinian local `Λ`-algebra `A`. -/
def predeformationFunctor :
    Predeformation.Obj f openImmersion kToS h_factor x0 ⥤ ArtinianLocalAlgCat Λ k :=
  Predeformation.forget f openImmersion kToS h_factor x0

/-- The labeled functor sends an object `x0 ⟶ x` over `Spec(A)` to `A`. -/
theorem predeformationFunctor_obj
    (ξ : Predeformation.Obj f openImmersion kToS h_factor x0) :
    (predeformationFunctor f openImmersion kToS h_factor x0).obj ξ = ξ.base :=
  sorry

/-- The opposite of `predeformationFunctor` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_predeformationFunctor :
    Functor.IsFibered.InGroupoids
      (predeformationFunctor f openImmersion kToS h_factor x0).op :=
  sorry

/-- The predeformation functor of `Complexes f` at a residue object is a deformation
category. -/
instance instIsDeformationCategory_predeformationFunctor :
    Functor.IsDeformationCategory
      (predeformationFunctor f openImmersion kToS h_factor x0) :=
  sorry

/-- The Artin tangent space `Tℱ_{X, k, x0}` is the type of isomorphism classes of
the dual-number fibre of `predeformationFunctor`. -/
abbrev tangentSpace :=
  (Functor.fiberIsoClassFunctor
      (predeformationFunctor f openImmersion kToS h_factor x0)).obj
    (dualNumber Λ k)

/-- `tangentSpace` is the type of isomorphism classes of the fibre over `k[ε]`. -/
theorem tangentSpace_def :
    tangentSpace f openImmersion kToS h_factor x0 =
      (Functor.fiberIsoClassFunctor
          (predeformationFunctor f openImmersion kToS h_factor x0)).obj
        (dualNumber Λ k) :=
  sorry

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
        (predeformationFunctor f openImmersion kToS h_factor x0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Complexes
