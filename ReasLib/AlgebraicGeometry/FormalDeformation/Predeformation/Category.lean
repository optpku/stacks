/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.CategoryTheory.Fibered.Groupoids.Bicategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Scheme

/-!
# The category `ℱ_{𝒳, k, x₀}` and its forgetful functor to `ArtinianLocalAlgCat`

Objects are morphisms `x₀ ⟶ x` in a category fibered in groupoids over `Over S`
with `x` lying over `Spec(A)` for `A` Artinian local over `Λ`. Morphisms are
commutative triangles with reversed arrows in the total category.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver.Predeformation

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (X : FiberedCategoryOver.Groupoids.{u + 1, u, u + 1, u} (Over S))
variable (x0 : X.p.Fiber (Over.mk kToS))

/-- An object of `ℱ_{𝒳, k, x₀}`: a morphism `x₀ ⟶ x` in `𝒳` lying over
`Spec(k) ⟶ Spec(A)` for some `A : ArtinianLocalAlgCat Λ k`. -/
structure Object where
  /-- The Artinian local `Λ`-algebra over which the target lies. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The target object `x` of `𝒳`, lying over `specOver base`. -/
  target : X.p.Fiber (specOver openImmersion base)
  /-- The morphism `x₀ ⟶ x` in the total category of `𝒳`. -/
  fromResidue : Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj target
  /-- `fromResidue` lies over `specOver_toResidue base`. -/
  over_fromResidue :
    X.p.IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue

/-- Construct an Artinian base, a fiber object, and a residue lift as explicit object data. -/
def Object.of (base : ArtinianLocalAlgCat Λ k)
    (target : X.p.Fiber (specOver openImmersion base))
    (fromResidue : Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj target)
    (over_fromResidue :
      X.p.IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue) :
    Object openImmersion kToS h_factor X x0 where
  base := base
  target := target
  fromResidue := fromResidue
  over_fromResidue := over_fromResidue

/-- The categorical carrier of residue lifts over Artinian local algebras. -/
def Obj := Object openImmersion kToS h_factor X x0

section

variable {openImmersion kToS h_factor X x0}

/-- The Artinian local base of a predeformation object. -/
def Obj.base (ξ : Obj openImmersion kToS h_factor X x0) : ArtinianLocalAlgCat Λ k :=
  Object.base ξ

/-- The target in the fiber over the spectrum of a predeformation's base. -/
def Obj.target (ξ : Obj openImmersion kToS h_factor X x0) :
    X.p.Fiber (specOver openImmersion ξ.base) :=
  Object.target ξ

/-- The arrow from the chosen residue object to the target of a predeformation. -/
def Obj.fromResidue (ξ : Obj openImmersion kToS h_factor X x0) :
    Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj ξ.target :=
  Object.fromResidue ξ

/-- The residue arrow of a predeformation lies over its residue spectrum map. -/
abbrev Obj.over_fromResidue (ξ : Obj openImmersion kToS h_factor X x0) :
    X.p.IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base) ξ.fromResidue :=
  Object.over_fromResidue ξ

end

/-- Bundle an Artinian base, a fiber object, and a residue lift as a predeformation. -/
def Obj.of (base : ArtinianLocalAlgCat Λ k)
    (target : X.p.Fiber (specOver openImmersion base))
    (fromResidue : Fiber.fiberInclusion.obj x0 ⟶ Fiber.fiberInclusion.obj target)
    (over_fromResidue :
      X.p.IsHomLift (specOver_toResidue openImmersion kToS h_factor base) fromResidue) :
    Obj openImmersion kToS h_factor X x0 :=
  Object.of openImmersion kToS h_factor X x0 base target fromResidue over_fromResidue

/-- An object of `ℱ_{𝒳, k, x₀}` is a morphism `x₀ ⟶ x` lying over
`specOver_toResidue`. -/
theorem Obj.spec (ξ : Obj openImmersion kToS h_factor X x0) :
    X.p.obj (Fiber.fiberInclusion.obj ξ.target) = specOver openImmersion ξ.base ∧
      X.p.IsHomLift (specOver_toResidue openImmersion kToS h_factor ξ.base)
        ξ.fromResidue :=
  sorry

section

variable {openImmersion kToS h_factor X x0}

/-- A morphism `(x₀ ⟶ x) ⟶ (x₀ ⟶ x')` in `ℱ_{𝒳, k, x₀}` is a commutative
triangle with reversed arrow `x' ⟶ x` in `𝒳`. -/
structure Arrow (ξ η : Obj openImmersion kToS h_factor X x0) where
  /-- The underlying morphism of Artinian local `Λ`-algebras. -/
  baseHom : ξ.base ⟶ η.base
  /-- The reversed arrow `η.target ⟶ ξ.target` in the total category of `𝒳`. -/
  hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target
  /-- `hom` lies over `specOverMap baseHom`. -/
  over_hom : X.p.IsHomLift (specOverMap openImmersion baseHom) hom
  /-- The triangle `ξ.fromResidue = η.fromResidue ≫ hom`. -/
  triangle : ξ.fromResidue = η.fromResidue ≫ hom

/-- Construct explicit morphism data from a base map and a compatible reversed triangle. -/
def Arrow.of {ξ η : Obj openImmersion kToS h_factor X x0} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom : X.p.IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) : Arrow ξ η where
  baseHom := baseHom
  hom := hom
  over_hom := over_hom
  triangle := triangle

/-- The categorical morphisms of predeformations are compatible reversed triangles. -/
def Hom (ξ η : Obj openImmersion kToS h_factor X x0) := Arrow ξ η

/-- The map of Artinian local bases underlying a predeformation morphism. -/
def Hom.baseHom {ξ η : Obj openImmersion kToS h_factor X x0} (morphism : Hom ξ η) :
    ξ.base ⟶ η.base :=
  Arrow.baseHom morphism

/-- The reversed arrow in the total category underlying a predeformation morphism. -/
def Hom.hom {ξ η : Obj openImmersion kToS h_factor X x0} (morphism : Hom ξ η) :
    Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target :=
  Arrow.hom morphism

/-- The reversed arrow of a predeformation morphism lies over its spectrum map. -/
abbrev Hom.over_hom {ξ η : Obj openImmersion kToS h_factor X x0} (morphism : Hom ξ η) :
    X.p.IsHomLift (specOverMap openImmersion morphism.baseHom) morphism.hom :=
  Arrow.over_hom morphism

/-- The reversed arrow of a predeformation morphism commutes with the residue arrows. -/
abbrev Hom.triangle {ξ η : Obj openImmersion kToS h_factor X x0} (morphism : Hom ξ η) :
    ξ.fromResidue = η.fromResidue ≫ morphism.hom :=
  Arrow.triangle morphism

/-- Bundle a base map and a compatible reversed triangle as a predeformation morphism. -/
def Hom.of {ξ η : Obj openImmersion kToS h_factor X x0} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom : X.p.IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) : Hom ξ η :=
  Arrow.of baseHom hom over_hom triangle

/-- The identity morphism of an object of `ℱ_{𝒳, k, x₀}`. -/
def Hom.id (ξ : Obj openImmersion kToS h_factor X x0) : Hom ξ ξ where
  baseHom := 𝟙 ξ.base
  hom := 𝟙 (Fiber.fiberInclusion.obj ξ.target)
  over_hom := sorry
  triangle := sorry

/-- Composition of morphisms of `ℱ_{𝒳, k, x₀}` composes base maps covariantly and
total-category arrows in reverse. -/
def Hom.comp {ξ η ζ : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) (g : Hom η ζ) :
    Hom ξ ζ where
  baseHom := f.baseHom ≫ g.baseHom
  hom := g.hom ≫ f.hom
  over_hom := sorry
  triangle := sorry

/-- A morphism of `ℱ_{𝒳, k, x₀}` is a base map together with a reversed triangle
in `𝒳`. -/
theorem Hom.spec {ξ η : Obj openImmersion kToS h_factor X x0} (f : Hom ξ η) :
    X.p.IsHomLift (specOverMap openImmersion f.baseHom) f.hom ∧
      ξ.fromResidue = η.fromResidue ≫ f.hom :=
  sorry

end

/-- The category `ℱ_{𝒳, k, x₀}` of morphisms `x₀ ⟶ x` over Artinian local
`Λ`-algebras. -/
instance category : Category.{u} (Obj openImmersion kToS h_factor X x0) where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp := sorry
  comp_id := sorry
  assoc := sorry

/-- The forgetful functor `p : ℱ_{𝒳, k, x₀} ⥤ ArtinianLocalAlgCat Λ k`. -/
def forget : Obj openImmersion kToS h_factor X x0 ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map f := f.baseHom
  map_id := sorry
  map_comp := sorry

/-- The object map of `forget` is the stored Artinian base. -/
theorem forget_obj (ξ : Obj openImmersion kToS h_factor X x0) :
    (forget openImmersion kToS h_factor X x0).obj ξ = ξ.base :=
  sorry

/-- The morphism map of `forget` is the stored base homomorphism. -/
theorem forget_map {ξ η : Obj openImmersion kToS h_factor X x0} (f : ξ ⟶ η) :
    (forget openImmersion kToS h_factor X x0).map f = f.baseHom :=
  sorry

/-- The fibre of `ℱ_{𝒳, k, x₀}` over an Artinian local `Λ`-algebra `A`. -/
def fiber (A : ArtinianLocalAlgCat Λ k) :=
  (forget openImmersion kToS h_factor X x0).Fiber A

/-- An object of the fibre over `A` is a morphism `x₀ ⟶ x` lying over
`specOver_toResidue A`. -/
theorem fiber_spec (A : ArtinianLocalAlgCat Λ k)
    (ξ : fiber openImmersion kToS h_factor X x0 A) :
    let x := Fiber.fiberInclusion.obj ξ
    x.base = A ∧
      X.p.IsHomLift (specOver_toResidue openImmersion kToS h_factor A) x.fromResidue :=
  sorry

end AlgebraicGeometry.GroupoidsOver.Predeformation
