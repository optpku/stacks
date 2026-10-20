module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.CategoryTheory.Fibered.Fiber.Hom

/-!
# Restriction in fibres over schemes

Chosen cartesian lifts define restriction of objects, arrows, and isomorphisms,
with identity and composition comparisons.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Functor

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳 : Type (u + 1)} [Category.{u} 𝒳]

/-- Restriction of a fibre object along a morphism of `S`-schemes, obtained from a
chosen cartesian lift. -/
def restrictObj {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    (ξ : p.Fiber U) (f : Z ⟶ U) : p.Fiber Z :=
  Fiber.mk (IsPreFibered.pullbackObj_proj ξ.property f)

/-- The underlying total object of `restrictObj` is the chosen cartesian pullback. -/
theorem restrictObj_val {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    (ξ : p.Fiber U) (f : Z ⟶ U) :
    (restrictObj ξ f).1 = IsPreFibered.pullbackObj ξ.property f := rfl

/-- Restriction along equal base morphisms gives canonically isomorphic fibre objects. -/
def restrictObj_eq {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    (ξ : p.Fiber U) {f g : Z ⟶ U} (h : f = g) :
    restrictObj ξ f ≅ restrictObj ξ g :=
  eqToIso (congrArg (restrictObj ξ) h)

/-- The unique comparison induced by a cartesian lift, with explicit certificates. -/
def cartesianMap {p : 𝒳 ⥤ Over S} {R T : Over S} {a b a' : 𝒳}
    (f : R ⟶ T) (φ : a ⟶ b) (hφ : p.IsCartesian f φ)
    (φ' : a' ⟶ b) (hφ' : p.IsHomLift f φ') : a' ⟶ a :=
  @IsCartesian.map (Over S) 𝒳 _ _ p R T a b f φ hφ a' φ' hφ'

/-- The comparison `cartesianMap` is vertical over the identity of the domain. -/
theorem cartesianMap_isHomLift {p : 𝒳 ⥤ Over S} {R T : Over S} {a b a' : 𝒳}
    (f : R ⟶ T) (φ : a ⟶ b) (hφ : p.IsCartesian f φ)
    (φ' : a' ⟶ b) (hφ' : p.IsHomLift f φ') :
    p.IsHomLift (𝟙 R) (cartesianMap f φ hφ φ' hφ') :=
  @IsCartesian.map_isHomLift (Over S) 𝒳 _ _ p R T a b f φ hφ a' φ' hφ'

/-- A fibre morphism over `U` restricts along `f : Z ⟶ U` by the universal property
of the chosen cartesian lift. -/
@[no_expose]
def restrictHom {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    {ξ ξ' : p.Fiber U} (φ : ξ ⟶ ξ') (f : Z ⟶ U) :
    restrictObj ξ f ⟶ restrictObj ξ' f :=
  let φX := IsPreFibered.pullbackMap ξ.property f
  let φY := IsPreFibered.pullbackMap ξ'.property f
  let φ' := φX ≫ φ.1
  let hφ' : p.IsHomLift f φ' :=
    @IsHomLift.comp_lift_id_right _ _ _ _ p _ _ _ _ _ f φX
      (IsPreFibered.pullbackMap.IsCartesian ξ.property f).toIsHomLift φ.1 φ.2
  Fiber.Hom.mk (cartesianMap f φY (IsPreFibered.pullbackMap.IsCartesian ξ'.property f) φ' hφ')
    (cartesianMap_isHomLift f φY (IsPreFibered.pullbackMap.IsCartesian ξ'.property f) φ' hφ')

/-- Restriction of a fibre isomorphism along a morphism of `S`-schemes. -/
def restrictIso {p : 𝒳 ⥤ Over S} [p.IsFibered] {U Z : Over S}
    {ξ ξ' : p.Fiber U} (e : ξ ≅ ξ') (f : Z ⟶ U) :
    restrictObj ξ f ≅ restrictObj ξ' f where
  hom := restrictHom e.hom f
  inv := restrictHom e.inv f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction along the identity recovers the original fibre object. -/
@[no_expose]
def restrictObj_id {p : 𝒳 ⥤ Over S} [p.IsFibered] {U : Over S}
    (ξ : p.Fiber U) : restrictObj ξ (𝟙 U) ≅ ξ :=
  let φ := IsPreFibered.pullbackMap ξ.property (𝟙 U)
  let hφ := IsPreFibered.pullbackMap.IsCartesian ξ.property (𝟙 U)
  let hid : p.IsHomLift (𝟙 U) (𝟙 ξ.1) := IsHomLift.id ξ.property
  { hom := Fiber.Hom.mk φ hφ.toIsHomLift
    inv := Fiber.Hom.mk (cartesianMap (𝟙 U) φ hφ (𝟙 ξ.1) hid)
      (cartesianMap_isHomLift (𝟙 U) φ hφ (𝟙 ξ.1) hid)
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Successive restrictions along `f` then `g` agree with restriction along `g ≫ f`. -/
def restrictObj_comp {p : 𝒳 ⥤ Over S} [p.IsFibered]
    {U V W : Over S} (ξ : p.Fiber U) (f : V ⟶ U) (g : W ⟶ V) :
    restrictObj (restrictObj ξ f) g ≅ restrictObj ξ (g ≫ f) :=
  let i := (IsFibered.pullbackPullbackIso ξ.property f g).symm
  { hom := Fiber.Hom.mk i.hom
      (IsCartesian.domainUniqueUpToIso_hom_isHomLift p (g ≫ f)
        (IsPreFibered.pullbackMap (IsPreFibered.pullbackObj_proj ξ.property f) g ≫
          IsPreFibered.pullbackMap ξ.property f)
        (IsPreFibered.pullbackMap ξ.property (g ≫ f)))
    inv := Fiber.Hom.mk i.inv
      (IsCartesian.domainUniqueUpToIso_inv_isHomLift p (g ≫ f)
        (IsPreFibered.pullbackMap (IsPreFibered.pullbackObj_proj ξ.property f) g ≫
          IsPreFibered.pullbackMap ξ.property f)
        (IsPreFibered.pullbackMap ξ.property (g ≫ f)))
    hom_inv_id := sorry
    inv_hom_id := sorry }

end AlgebraicGeometry.FiniteHilbertStack
