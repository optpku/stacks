module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.Category.Cat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CohStack.Groupoids
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Scheme
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.TangentSpace.Tensor
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Unpointed
public import ReasLib.AlgebraicGeometry.FormalDeformation.RimSchlessinger.Schlessinger
public import ReasLib.AlgebraicGeometry.FormalDeformation.Schlessinger.FiberIsoClass

/-!
# The predeformation category of `Coh_{X/B}` at a residue object

Objects of `ℱ_{Coh_{X/B}, k, x0}` are morphisms `x0 ⟶ x` in `CohStack f` lying
over `Spec(k) ⟶ Spec(A)` for `A` Artinian local over `Λ`. The forgetful functor
lands in `ArtinianLocalAlgCat Λ k`. Residue-lift objects and compatible reversed triangles form an explicit
bundled category with its projection to Artinian local algebras.
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
structure Object where
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


section

variable {f openImmersion kToS h_factor x0}

/-- A morphism `(x0 ⟶ x) ⟶ (x0 ⟶ x')` in `ℱ_{Coh_{X/B}, k, x0}` is a
commutative triangle with reversed arrow `x' ⟶ x` in `CohStack f`. -/
structure Hom (ξ η : Object f openImmersion kToS h_factor x0) where
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
def Hom.of {ξ η : Object f openImmersion kToS h_factor x0} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom : (p f).IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) : Hom ξ η where
  baseHom := baseHom
  hom := hom
  over_hom := over_hom
  triangle := triangle

/-- The identity morphism of an object of `ℱ_{Coh_{X/B}, k, x0}`. -/
def Hom.id (ξ : Object f openImmersion kToS h_factor x0) : Hom ξ ξ :=
  let laws :
      (p f).IsHomLift (specOverMap openImmersion (𝟙 ξ.base))
        (𝟙 (Fiber.fiberInclusion.obj ξ.target)) ∧
      ξ.fromResidue = ξ.fromResidue ≫ 𝟙 (Fiber.fiberInclusion.obj ξ.target) := sorry
  Hom.of (𝟙 ξ.base) (𝟙 (Fiber.fiberInclusion.obj ξ.target)) laws.1 laws.2

/-- Composition of morphisms of `ℱ_{Coh_{X/B}, k, x0}` composes base maps
covariantly and total-category arrows in reverse. -/
def Hom.comp {ξ η ζ : Object f openImmersion kToS h_factor x0} (α : Hom ξ η)
    (β : Hom η ζ) : Hom ξ ζ :=
  let laws :
      (p f).IsHomLift (specOverMap openImmersion (α.baseHom ≫ β.baseHom))
        (β.hom ≫ α.hom) ∧
      ξ.fromResidue = ζ.fromResidue ≫ (β.hom ≫ α.hom) := sorry
  Hom.of (α.baseHom ≫ β.baseHom) (β.hom ≫ α.hom) laws.1 laws.2

/-- A morphism of `ℱ_{Coh_{X/B}, k, x0}` is a base map together with a reversed
triangle in `CohStack f`. -/
theorem Hom.spec {ξ η : Object f openImmersion kToS h_factor x0} (α : Hom ξ η) :
    (p f).IsHomLift (specOverMap openImmersion α.baseHom) α.hom ∧
      ξ.fromResidue = η.fromResidue ≫ α.hom :=
  sorry

end

/-- The category `ℱ_{Coh_{X/B}, k, x0}` of morphisms `x0 ⟶ x` over Artinian
local `Λ`-algebras. -/
def category : Cat.{u + 1, u + 1} :=
  let laws :
      (∀ {ξ η : Object f openImmersion kToS h_factor x0} (α : Hom ξ η),
        Hom.comp (Hom.id ξ) α = α) ∧
      (∀ {ξ η : Object f openImmersion kToS h_factor x0} (α : Hom ξ η),
        Hom.comp α (Hom.id η) = α) ∧
      (∀ {ξ η ζ ω : Object f openImmersion kToS h_factor x0}
        (α : Hom ξ η) (β : Hom η ζ) (γ : Hom ζ ω),
        Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ)) := sorry
  ⟨Object f openImmersion kToS h_factor x0, {
    Hom := Hom
    id := Hom.id
    comp := Hom.comp
    id_comp := laws.1
    comp_id := laws.2.1
    assoc := laws.2.2 }⟩

/-- The categorical carrier of residue lifts over Artinian local algebras. -/
abbrev Obj : Type (u + 1) := category f openImmersion kToS h_factor x0

section

variable {f openImmersion kToS h_factor x0}

/-- The Artinian local base of a residue lift. -/
def Obj.base (ξ : Obj f openImmersion kToS h_factor x0) : ArtinianLocalAlgCat Λ k :=
  Object.base ξ

/-- The target object in the fibre over the spectrum of a residue lift's base. -/
def Obj.target (ξ : Obj f openImmersion kToS h_factor x0) :
    (p f).Fiber (specOver openImmersion ξ.base) :=
  Object.target ξ

/-- The arrow from the residue object to the target of a residue lift. -/
def Obj.fromResidue (ξ : Obj f openImmersion kToS h_factor x0) :
    Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj ξ.target :=
  Object.fromResidue ξ

/-- The arrow from the residue object lies over the residue spectrum map. -/
abbrev Obj.over_fromResidue (ξ : Obj f openImmersion kToS h_factor x0) :
    (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base)
      ξ.fromResidue :=
  Object.over_fromResidue ξ

end

/-- Construct a categorical residue lift from its base, target, and residue arrow. -/
def Obj.of (base : ArtinianLocalAlgCat Λ k)
    (target : (p f).Fiber (specOver openImmersion base))
    (fromResidue : Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj target)
    (over_fromResidue :
      (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue) :
    Obj f openImmersion kToS h_factor x0 :=
  Object.of f openImmersion kToS h_factor x0 base target fromResidue over_fromResidue

/-- An object of `ℱ_{Coh_{X/B}, k, x0}` is a morphism `x0 ⟶ x` lying over
`specOver_toResidue`. -/
theorem Obj.spec (ξ : Obj f openImmersion kToS h_factor x0) :
    (p f).obj (Fiber.fiberInclusion.obj ξ.target) = specOver openImmersion ξ.base ∧
      (p f).IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base)
        ξ.fromResidue :=
  sorry

end Predeformation

/-- The predeformation functor `ℱ_{Coh_{X/B}, k, x0} ⥤ ArtinianLocalAlgCat Λ k`
associated to an object `x0` of `CohStack f` over a finite-type field `k`. -/
def predeformation :
    Predeformation.Obj f openImmersion kToS h_factor x0 ⥤ ArtinianLocalAlgCat Λ k :=
  let laws :
      (∀ ξ : Predeformation.Obj f openImmersion kToS h_factor x0,
        (Predeformation.Hom.id ξ).baseHom = 𝟙 ξ.base) ∧
      (∀ {ξ η ζ : Predeformation.Obj f openImmersion kToS h_factor x0}
        (α : ξ ⟶ η) (β : η ⟶ ζ),
        (Predeformation.Hom.comp α β).baseHom = α.baseHom ≫ β.baseHom) := sorry
  { obj := fun ξ => ξ.base
    map := fun α => α.baseHom
    map_id := laws.1
    map_comp := laws.2 }

/-- The object map of `predeformation` is the stored Artinian base. -/
theorem predeformation_obj (ξ : Predeformation.Obj f openImmersion kToS h_factor x0) :
    (predeformation f openImmersion kToS h_factor x0).obj ξ = ξ.base :=
  sorry

/-- The morphism map of the predeformation projection is the stored base map. -/
theorem predeformation_map {ξ η : Predeformation.Obj f openImmersion kToS h_factor x0}
    (α : ξ ⟶ η) :
    (predeformation f openImmersion kToS h_factor x0).map α = α.baseHom := sorry

/-- The predeformation functor of `CohStack f` at a residue object is a
deformation category. -/
instance instIsDeformationCategory_predeformation :
    Functor.IsDeformationCategory (predeformation f openImmersion kToS h_factor x0) :=
  sorry

/-- The tangent space is the isomorphism classes in the dual-number fibre of the
coherent-sheaf predeformation projection. -/
abbrev tangentSpace :=
  (Functor.fiberIsoClassFunctor (predeformation f openImmersion kToS h_factor x0)).obj
    (ArtinianLocalAlgCat.dualNumber Λ k)

/-- The infinitesimal automorphism space of the coherent-sheaf predeformation projection. -/
abbrev infinitesimalAutomorphisms :=
  Functor.infinitesimalAutomorphisms (predeformation f openImmersion kToS h_factor x0)

end AlgebraicGeometry.AlgebraicSpace.CohStack
