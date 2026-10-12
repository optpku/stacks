/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import stacks_project.Chap90.Definition_90_16_8
public import stacks_project.Chap98.«98_3_0_2_SpecOver»
public import stacks_project.Chap99.Lemma_99_5_2

/-!
# The predeformation category of `Coh_{X/B}` at a residue object

Objects of `ℱ_{Coh_{X/B}, k, x0}` are morphisms `x0 ⟶ x` in `CohStack f` lying
over `Spec(k) ⟶ Spec(A)` for `A` Artinian local over `Λ`. The forgetful functor
lands in `ArtinianLocalAlgCat Λ k`. Hom-types of `Obj f` live in `Type (u + 1)`,
so this is not an instance of the Chap98 `predeformationFunctor`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Functor
open AlgebraicGeometry.GroupoidsOver.Predeformation

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.CohStack

variable {S : Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian S]
variable {X B : AlgebraicSpace S} (f : X ⟶ B) [FinitePresentation f]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [AlgebraicGeometry.IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x0 : (p f).Fiber (Over.mk kToS))

namespace Predeformation

/-- An object of `ℱ_{Coh_{X/B}, k, x0}`: a morphism `x0 ⟶ x` in `CohStack f`
lying over `Spec(k) ⟶ Spec(A)` for some `A : ArtinianLocalAlgCat Λ k`. -/
structure Obj where
  /-- The Artinian local `Λ`-algebra over which the target lies. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The target object `x` of `CohStack f`, lying over `specOver base`. -/
  target : (p f).Fiber (specOver openImmersion base)
  /-- The morphism `x0 ⟶ x` in the total category of `CohStack f`. -/
  fromResidue : Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj target
  /-- `fromResidue` lies over `specOver_toResidue base`. -/
  over_fromResidue :
    (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue

/-- Bundle an Artinian base, a fibre object, and a lift of `x0` into an object of
`ℱ_{Coh_{X/B}, k, x0}`. -/
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

/-- An object of `ℱ_{Coh_{X/B}, k, x0}` is a morphism `x0 ⟶ x` lying over
`specOver_toResidue`. -/
theorem Obj.spec (ξ : Obj f openImmersion kToS h_factor x0) :
    (p f).obj (Fiber.fiberInclusion.obj ξ.target) = specOver openImmersion ξ.base ∧
      (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base)
        ξ.fromResidue :=
  sorry

section

variable {f openImmersion kToS h_factor x0}

/-- A morphism `(x0 ⟶ x) ⟶ (x0 ⟶ x')` in `ℱ_{Coh_{X/B}, k, x0}` is a
commutative triangle with reversed arrow `x' ⟶ x` in `CohStack f`. -/
structure Hom (ξ η : Obj f openImmersion kToS h_factor x0) where
  /-- The underlying morphism of Artinian local `Λ`-algebras. -/
  baseHom : ξ.base ⟶ η.base
  /-- The reversed arrow `η.target ⟶ ξ.target` in the total category. -/
  hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target
  /-- `hom` lies over `specOverMap baseHom`. -/
  over_hom : (p f).IsHomLift (specOverMap openImmersion baseHom) hom
  /-- The triangle `ξ.fromResidue = η.fromResidue ≫ hom`. -/
  triangle : ξ.fromResidue = η.fromResidue ≫ hom

/-- Bundle a base morphism and a reversed total-category arrow into a morphism of
`ℱ_{Coh_{X/B}, k, x0}`. -/
def Hom.of {ξ η : Obj f openImmersion kToS h_factor x0} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom : (p f).IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) : Hom ξ η where
  baseHom := baseHom
  hom := hom
  over_hom := over_hom
  triangle := triangle

/-- The identity morphism of an object of `ℱ_{Coh_{X/B}, k, x0}`. -/
def Hom.id (ξ : Obj f openImmersion kToS h_factor x0) : Hom ξ ξ where
  baseHom := 𝟙 ξ.base
  hom := 𝟙 (Fiber.fiberInclusion.obj ξ.target)
  over_hom := sorry
  triangle := sorry

/-- Composition of morphisms of `ℱ_{Coh_{X/B}, k, x0}` composes base maps
covariantly and total-category arrows in reverse. -/
def Hom.comp {ξ η ζ : Obj f openImmersion kToS h_factor x0} (α : Hom ξ η)
    (β : Hom η ζ) : Hom ξ ζ where
  baseHom := α.baseHom ≫ β.baseHom
  hom := β.hom ≫ α.hom
  over_hom := sorry
  triangle := sorry

/-- A morphism of `ℱ_{Coh_{X/B}, k, x0}` is a base map together with a reversed
triangle in `CohStack f`. -/
theorem Hom.spec {ξ η : Obj f openImmersion kToS h_factor x0} (α : Hom ξ η) :
    (p f).IsHomLift (specOverMap openImmersion α.baseHom) α.hom ∧
      ξ.fromResidue = η.fromResidue ≫ α.hom :=
  sorry

end

/-- The category `ℱ_{Coh_{X/B}, k, x0}` of morphisms `x0 ⟶ x` over Artinian
local `Λ`-algebras. -/
instance category : Category.{u + 1} (Obj f openImmersion kToS h_factor x0) where
  Hom := Hom
  id := Hom.id
  comp α β := Hom.comp α β
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The forgetful functor `ℱ_{Coh_{X/B}, k, x0} ⥤ ArtinianLocalAlgCat Λ k`. -/
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

/-- The predeformation functor `ℱ_{Coh_{X/B}, k, x0} ⥤ ArtinianLocalAlgCat Λ k`
associated to an object `x0` of `CohStack f` over a finite-type field `k`. -/
def predeformation :
    Predeformation.Obj f openImmersion kToS h_factor x0 ⥤ ArtinianLocalAlgCat Λ k :=
  Predeformation.forget f openImmersion kToS h_factor x0

/-- The object map of `predeformation` is the stored Artinian base. -/
theorem predeformation_obj (ξ : Predeformation.Obj f openImmersion kToS h_factor x0) :
    (predeformation f openImmersion kToS h_factor x0).obj ξ = ξ.base :=
  sorry

/-- The predeformation functor of `CohStack f` at a residue object is a
deformation category. -/
instance instIsDeformationCategory_predeformation :
    Functor.IsDeformationCategory (predeformation f openImmersion kToS h_factor x0) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.CohStack
