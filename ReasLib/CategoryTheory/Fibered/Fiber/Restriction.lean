module

public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import ReasLib.CategoryTheory.Fibered.Fiber.Hom
public import ReasLib.CategoryTheory.Fibered.Fiber.Isomorphism

/-!
# Restriction of fibre objects along a base morphism

Chosen cartesian lifts define restriction of fibre objects, morphisms, and isomorphisms,
with canonical comparisons for identity and composite base morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

noncomputable section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory.Functor.Fiber

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

/-- Restriction of a fibre object along a morphism of the base, obtained from a chosen
cartesian lift. -/
def restrictObj {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U Z : 𝒮} (ξ : p.Fiber U) (f : Z ⟶ U) :
    p.Fiber Z :=
  Fiber.mk (IsPreFibered.pullbackObj_proj ξ.property f)

/-- The underlying total object of `restrictObj` is the chosen cartesian pullback. -/
theorem restrictObj_val {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U Z : 𝒮} (ξ : p.Fiber U)
    (f : Z ⟶ U) :
    (restrictObj ξ f).1 = IsPreFibered.pullbackObj ξ.property f := sorry

/-- Restriction along equal base morphisms yields canonically isomorphic fibre objects. -/
def restrictObj_eq {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U Z : 𝒮} (ξ : p.Fiber U)
    {f g : Z ⟶ U} (h : f = g) : restrictObj ξ f ≅ restrictObj ξ g :=
  eqToIso (congrArg (restrictObj ξ) h)

/-- The unique comparison induced by a cartesian lift, with explicit certificates. -/
def cartesianMap {p : 𝒳 ⥤ 𝒮} {R T : 𝒮} {a b a' : 𝒳} (f : R ⟶ T) (φ : a ⟶ b)
    (hφ : p.IsCartesian f φ) (φ' : a' ⟶ b) (hφ' : p.IsHomLift f φ') : a' ⟶ a :=
  @IsCartesian.map 𝒮 𝒳 _ _ p R T a b f φ hφ a' φ' hφ'

/-- The comparison `cartesianMap` is vertical over the identity of the domain. -/
theorem cartesianMap_isHomLift {p : 𝒳 ⥤ 𝒮} {R T : 𝒮} {a b a' : 𝒳} (f : R ⟶ T)
    (φ : a ⟶ b) (hφ : p.IsCartesian f φ) (φ' : a' ⟶ b) (hφ' : p.IsHomLift f φ') :
    p.IsHomLift (𝟙 R) (cartesianMap f φ hφ φ' hφ') :=
  @IsCartesian.map_isHomLift 𝒮 𝒳 _ _ p R T a b f φ hφ a' φ' hφ'

/-- A fibre morphism over `U` restricts along `f : Z ⟶ U` by the universal property of
the chosen cartesian lift. -/
def restrictHom {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U Z : 𝒮} {ξ ξ' : p.Fiber U}
    (φ : ξ ⟶ ξ') (f : Z ⟶ U) : restrictObj ξ f ⟶ restrictObj ξ' f :=
  let φX := IsPreFibered.pullbackMap ξ.property f
  let φY := IsPreFibered.pullbackMap ξ'.property f
  let φ' := φX ≫ φ.1
  let hφ' : p.IsHomLift f φ' :=
    @IsHomLift.comp_lift_id_right _ _ _ _ p _ _ _ _ _ f φX
      (IsPreFibered.pullbackMap.IsCartesian ξ.property f).toIsHomLift φ.1 φ.2
  Fiber.Hom.mk
    (cartesianMap f φY (IsPreFibered.pullbackMap.IsCartesian ξ'.property f) φ' hφ')
    (cartesianMap_isHomLift f φY (IsPreFibered.pullbackMap.IsCartesian ξ'.property f) φ' hφ')

/-- Restriction of a fibre isomorphism along a morphism of the base. -/
def restrictIso {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U Z : 𝒮} {ξ ξ' : p.Fiber U}
    (e : ξ ≅ ξ') (f : Z ⟶ U) : restrictObj ξ f ≅ restrictObj ξ' f where
  hom := restrictHom e.hom f
  inv := restrictHom e.inv f
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- Restriction along the identity recovers the original fibre object. -/
def restrictObj_id {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U : 𝒮} (ξ : p.Fiber U) :
    restrictObj ξ (𝟙 U) ≅ ξ :=
  let φ := IsPreFibered.pullbackMap ξ.property (𝟙 U)
  let hφ := IsPreFibered.pullbackMap.IsCartesian ξ.property (𝟙 U)
  let hid : p.IsHomLift (𝟙 U) (𝟙 ξ.1) := IsHomLift.id ξ.property
  { hom := Fiber.Hom.mk φ hφ.toIsHomLift
    inv := Fiber.Hom.mk (cartesianMap (𝟙 U) φ hφ (𝟙 ξ.1) hid)
      (cartesianMap_isHomLift (𝟙 U) φ hφ (𝟙 ξ.1) hid)
    hom_inv_id := sorry
    inv_hom_id := sorry }

/-- Successive restrictions along `f` then `g` agree with restriction along `g ≫ f`. -/
def restrictObj_comp {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U V W : 𝒮} (ξ : p.Fiber U)
    (f : V ⟶ U) (g : W ⟶ V) :
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

end CategoryTheory.Functor.Fiber
