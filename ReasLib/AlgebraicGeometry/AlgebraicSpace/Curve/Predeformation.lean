module

public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import ReasLib.AlgebraicGeometry.FormalDeformation.DeformationCategory
public import ReasLib.AlgebraicGeometry.FormalDeformation.InfinitesimalAutomorphisms.Predeformation
public import ReasLib.CategoryTheory.Cofibered.FiberIsoClass
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Scheme
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Category

/-!
# Predeformations of curves

Residue lifts over Artinian local algebras form an explicit bundled category.
Its projection gives the predeformation functor, whose dual-number fibre and
infinitesimal automorphisms are the Artin deformation spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor
open AlgebraicGeometry.AlgebraicSpace.Spaces
open AlgebraicGeometry.GroupoidsOver.Predeformation (specOver specOverMap specOver_toResidue)
open ArtinianLocalAlgCat

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces
namespace Curves

variable {S : Scheme.{u}} [IsLocallyNoetherian S]
variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
  [AlgebraicGeometry.IsOpenImmersion openImmersion]
variable (kToS : Spec (CommRingCat.of k) ⟶ S)
  [AlgebraicGeometry.LocallyOfFiniteType kToS]
variable (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
variable (x : (p S).Fiber (Over.mk kToS))

namespace Predeformation

/-- An object of `ℱ_{Curves, k, x}`: a morphism `x ⟶ ξ` in
`Curves.Obj S` lying over `Spec(k) ⟶ Spec(A)` for some
`A : ArtinianLocalAlgCat Λ k`. -/
structure Obj where
  /-- The Artinian local `Λ`-algebra over which the target lies. -/
  base : ArtinianLocalAlgCat Λ k
  /-- The target object of `Curves.p S`, lying over `specOver base`. -/
  target : (p S).Fiber (specOver openImmersion base)
  /-- The morphism `x ⟶ target` in the total category of `Curves.p S`. -/
  fromResidue :
    Fiber.fiberInclusion.obj x ⟶ Fiber.fiberInclusion.obj target
  /-- `fromResidue` lies over `specOver_toResidue base`. -/
  over_fromResidue :
    (p S).IsHomLift
      (specOver_toResidue openImmersion kToS h_factor base) fromResidue

/-- Bundle an Artinian base, a fibre object, and a lift of `x` into an object of
`ℱ_{Curves, k, x}`. -/
def Obj.of (base : ArtinianLocalAlgCat Λ k)
    (target : (p S).Fiber (specOver openImmersion base))
    (fromResidue :
      Fiber.fiberInclusion.obj x ⟶ Fiber.fiberInclusion.obj target)
    (over_fromResidue :
      (p S).IsHomLift
        (specOver_toResidue openImmersion kToS h_factor base) fromResidue) :
    Obj openImmersion kToS h_factor x where
  base := base
  target := target
  fromResidue := fromResidue
  over_fromResidue := over_fromResidue

/-- An object of `ℱ_{Curves, k, x}` is a morphism `x ⟶ ξ`
lying over `specOver_toResidue`. -/
theorem Obj.spec (ξ : Obj openImmersion kToS h_factor x) :
    (p S).obj (Fiber.fiberInclusion.obj ξ.target) =
        specOver openImmersion ξ.base ∧
      (p S).IsHomLift
        (specOver_toResidue openImmersion kToS h_factor ξ.base) ξ.fromResidue :=
  ⟨ξ.target.property, ξ.over_fromResidue⟩

section

variable {openImmersion kToS h_factor x}

/-- A morphism `(x ⟶ ξ) ⟶ (x ⟶ η)` in `ℱ_{Curves, k, x}` is a
commutative triangle with reversed arrow `η.target ⟶ ξ.target`. -/
structure Hom (ξ η : Obj openImmersion kToS h_factor x) where
  /-- The underlying morphism of Artinian local `Λ`-algebras. -/
  baseHom : ξ.base ⟶ η.base
  /-- The reversed arrow `η.target ⟶ ξ.target` in the total category. -/
  hom :
    Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target
  /-- `hom` lies over `specOverMap baseHom`. -/
  over_hom :
    (p S).IsHomLift (specOverMap openImmersion baseHom) hom
  /-- The triangle `ξ.fromResidue = η.fromResidue ≫ hom`. -/
  triangle : ξ.fromResidue = η.fromResidue ≫ hom

/-- Bundle a base morphism and a reversed total-category arrow into a morphism of
`ℱ_{Curves, k, x}`. -/
def Hom.of {ξ η : Obj openImmersion kToS h_factor x} (baseHom : ξ.base ⟶ η.base)
    (hom : Fiber.fiberInclusion.obj η.target ⟶ Fiber.fiberInclusion.obj ξ.target)
    (over_hom :
      (p S).IsHomLift (specOverMap openImmersion baseHom) hom)
    (triangle : ξ.fromResidue = η.fromResidue ≫ hom) : Hom ξ η where
  baseHom := baseHom
  hom := hom
  over_hom := over_hom
  triangle := triangle

/-- The identity morphism of an object of `ℱ_{Curves, k, x}`. -/
def Hom.id (ξ : Obj openImmersion kToS h_factor x) : Hom ξ ξ := by
  have laws :
      (p S).IsHomLift (specOverMap openImmersion (𝟙 ξ.base))
        (𝟙 (Fiber.fiberInclusion.obj ξ.target)) ∧
      ξ.fromResidue = ξ.fromResidue ≫ 𝟙 (Fiber.fiberInclusion.obj ξ.target) := by
    sorry
  exact Hom.of (𝟙 ξ.base) (𝟙 (Fiber.fiberInclusion.obj ξ.target)) laws.1 laws.2

/-- Composition of residue lifts composes base maps covariantly and
reverses the order of the total-category arrows. -/
def Hom.comp {ξ η ζ : Obj openImmersion kToS h_factor x} (α : Hom ξ η)
    (β : Hom η ζ) : Hom ξ ζ := by
  have laws :
      (p S).IsHomLift (specOverMap openImmersion (α.baseHom ≫ β.baseHom))
        (β.hom ≫ α.hom) ∧
      ξ.fromResidue = ζ.fromResidue ≫ (β.hom ≫ α.hom) := by
    sorry
  exact Hom.of (α.baseHom ≫ β.baseHom) (β.hom ≫ α.hom) laws.1 laws.2

/-- A morphism of `ℱ_{Curves, k, x}` is a base map together
with a reversed triangle in `Curves.Obj S`. -/
theorem Hom.spec {ξ η : Obj openImmersion kToS h_factor x} (α : Hom ξ η) :
    (p S).IsHomLift (specOverMap openImmersion α.baseHom)
        α.hom ∧
      ξ.fromResidue = η.fromResidue ≫ α.hom :=
  ⟨α.over_hom, α.triangle⟩

end

/-- The category of residue lifts of a curve over Artinian local algebras,
with compatible reversed triangles as morphisms. -/
def category : Cat.{u + 1, u + 1} := by
  have laws :
      (∀ {ξ η : Obj openImmersion kToS h_factor x} (α : Hom ξ η),
        Hom.comp (Hom.id ξ) α = α) ∧
      (∀ {ξ η : Obj openImmersion kToS h_factor x} (α : Hom ξ η),
        Hom.comp α (Hom.id η) = α) ∧
      (∀ {ξ η ζ ω : Obj openImmersion kToS h_factor x}
        (α : Hom ξ η) (β : Hom η ζ) (γ : Hom ζ ω),
        Hom.comp (Hom.comp α β) γ = Hom.comp α (Hom.comp β γ)) := by
    sorry
  exact ⟨Obj openImmersion kToS h_factor x, {
    Hom := Hom
    id := Hom.id
    comp := Hom.comp
    id_comp := laws.1
    comp_id := laws.2.1
    assoc := laws.2.2 }⟩

/-- The forgetful functor `ℱ_{Curves, k, x} ⥤
ArtinianLocalAlgCat Λ k`. -/
def forget : category openImmersion kToS h_factor x ⥤ ArtinianLocalAlgCat Λ k where
  obj ξ := ξ.base
  map α := α.baseHom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The object map of `forget` is the stored Artinian base. -/
theorem forget_obj (ξ : Obj openImmersion kToS h_factor x) :
    (forget openImmersion kToS h_factor x).obj ξ = ξ.base :=
  rfl

/-- The morphism map of `forget` is the stored base homomorphism. -/
theorem forget_map {ξ η : category openImmersion kToS h_factor x} (α : ξ ⟶ η) :
    (forget openImmersion kToS h_factor x).map α = α.baseHom :=
  rfl

end Predeformation

/-- The predeformation functor associated to a residue object of
`Curves.p S`, sending a morphism `x ⟶ ξ` over `Spec(A)` to the
Artinian local `Λ`-algebra `A`. -/
def predeformationFunctor :
    Predeformation.category openImmersion kToS h_factor x ⥤ ArtinianLocalAlgCat Λ k :=
  Predeformation.forget openImmersion kToS h_factor x

/-- The predeformation functor sends an object `x ⟶ ξ` over `Spec(A)` to `A`. -/
theorem predeformationFunctor_obj
    (ξ : Predeformation.Obj openImmersion kToS h_factor x) :
    (predeformationFunctor openImmersion kToS h_factor x).obj ξ = ξ.base :=
  rfl

/-- The opposite of `predeformationFunctor` is cofibered in groupoids. -/
instance instIsFiberedInGroupoids_predeformationFunctor :
    Functor.IsFibered.InGroupoids
      (predeformationFunctor openImmersion kToS h_factor x).op :=
  sorry

/-- The predeformation functor of `Curves.p` at a residue object is
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

/-- The infinitesimal automorphism space `Inf(ℱ_{𝒳, k, x})` of the predeformation
functor of `Curves.p` at `x`. -/
abbrev infinitesimalAutomorphisms :=
  Functor.infinitesimalAutomorphisms
    (predeformationFunctor openImmersion kToS h_factor x)

end Curves
end AlgebraicGeometry.AlgebraicSpace.Spaces
