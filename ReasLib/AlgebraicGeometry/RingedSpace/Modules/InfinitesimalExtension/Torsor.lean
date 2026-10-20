module

public import Mathlib.Algebra.Torsor.Defs
public import ReasLib.CategoryTheory.Abelian.Extension.Classification
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension

/-!
# Torsor of infinitesimal extensions

Along a first-order thickening, isomorphism classes of extensions with a fixed
infinitesimal map form a principal homogeneous space under Baer sum with
`𝒪_X`-extension classes, canonically identified with `Ext¹` by
`ExtensionClass.toExt`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X X' : RingedSpace.{u}}
variable {i : X ⟶ X'} [IsFirstOrderThickening i]
variable {F K : X.Modules}
variable {c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K}

/-- The underlying mixed-scalar short exact sequence of an extension. -/
def toExtension (E : InfinitesimalExtension i F K c) :
    Extension ((i _*).obj K) ((i _*).obj F) where
  E := E.module
  f := E.ι
  g := E.π
  zero := E.w
  shortExact := E.shortExact

/-- The underlying extension has the same middle object and endpoint maps. -/
theorem toExtension_spec (E : InfinitesimalExtension i F K c) :
    (toExtension E).E = E.module ∧ (toExtension E).f = E.ι ∧ (toExtension E).g = E.π :=
  sorry

/-- Two extensions with the same infinitesimal map are equivalent when there is a
morphism between them. -/
def isoSetoid (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    Setoid (InfinitesimalExtension i F K c) where
  r E₁ E₂ := Nonempty (Hom E₁ E₂)
  iseqv := sorry

/-- Isomorphism classes of extensions of `ℱ` by `𝒦` with infinitesimal map `c`. -/
abbrev IsoClass (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :=
  Quotient (isoSetoid i F K c)

namespace IsoClass

/-- The isomorphism class of a given extension. -/
def mk (E : InfinitesimalExtension i F K c) : IsoClass i F K c :=
  Quotient.mk (isoSetoid i F K c) E

/-- A morphism of extensions identifies their isomorphism classes. -/
theorem mk_eq_mk_of_hom {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    mk E₁ = mk E₂ := sorry

end IsoClass

/-- Direct image of an `𝒪_X`-module extension along a first-order thickening. -/
def pushforwardExtension (i : X ⟶ X') [IsFirstOrderThickening i] (S : Extension K F) :
    Extension ((i _*).obj K) ((i _*).obj F) where
  E := (i _*).obj S.E
  f := (i _*).map S.f
  g := (i _*).map S.g
  zero := by rw [← Functor.map_comp, S.zero, Functor.map_zero]
  shortExact := sorry

/-- Direct image of an `𝒪_X`-extension class along a first-order thickening. -/
def pushforwardClass (i : X ⟶ X') [IsFirstOrderThickening i] (ξ : ExtensionClass K F) :
    ExtensionClass ((i _*).obj K) ((i _*).obj F) :=
  _root_.Quotient.map (pushforwardExtension i) sorry ξ

/-- Adding a pushed-forward `𝒪_X`-extension does not change the infinitesimal map. -/
def vaddExt (S : Extension K F) (E : InfinitesimalExtension i F K c) :
    InfinitesimalExtension i F K c :=
  let T := Extension.baerSum (pushforwardExtension i S) (toExtension E)
  { module := T.E
    ι := T.f
    π := T.g
    w := T.zero
    shortExact := T.shortExact
    infMap_eq := sorry }

/-- The infinitesimal map of `vaddExt S E` equals the prescribed `c`. -/
theorem infMap_vadd (S : Extension K F) (E : InfinitesimalExtension i F K c) :
    infinitesimalMap i (vaddExt S E).ι (vaddExt S E).π (vaddExt S E).w
      (vaddExt S E).shortExact = c := sorry

/-- The `𝒪_X`-extension obtained as the Baer difference of two extensions with the same
`c`, after descending the middle term along `i` using that it is annihilated by `ℐ`. -/
def vsubExt (E₁ E₂ : InfinitesimalExtension i F K c) : Extension K F :=
  let D := Extension.baerSum (toExtension E₁) (Extension.neg (toExtension E₂))
  let f := (asIso ((pullbackPushforwardAdjunction i).counit.app K)).inv ≫ (i ^*).map D.f
  let g := (i ^*).map D.g ≫ (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom
  have laws : f ≫ g = 0 ∧ ∀ h : f ≫ g = 0, (ShortComplex.mk f g h).ShortExact := by
    sorry
  { E := (i ^*).obj D.E
    f := f
    g := g
    zero := laws.1
    shortExact := laws.2 laws.1 }

/-- Baer-sum action of an `𝒪_X`-extension class on an isomorphism class. -/
def vadd (ξ : ExtensionClass K F) (p : IsoClass i F K c) : IsoClass i F K c :=
  _root_.Quotient.map₂ (fun S E ↦ vaddExt S E) sorry ξ p

/-- Baer difference of two isomorphism classes, as an `𝒪_X`-extension class. -/
def vsub (p q : IsoClass i F K c) : ExtensionClass K F :=
  _root_.Quotient.map₂ (fun E₁ E₂ ↦ vsubExt E₁ E₂) sorry p q

/-- Baer sum of `𝒪_X`-extension classes acts on isomorphism classes. -/
instance instVAdd_isoClass : VAdd (ExtensionClass K F) (IsoClass i F K c) where
  vadd := vadd

/-- Difference of isomorphism classes is an `𝒪_X`-extension class. -/
instance instVSub_isoClass : VSub (ExtensionClass K F) (IsoClass i F K c) where
  vsub := vsub

/-- The Baer-sum action of `𝒪_X`-extension classes on isomorphism classes. -/
instance instAddAction_isoClass : AddAction (ExtensionClass K F) (IsoClass i F K c) := by
  have laws :
      (∀ (ξ η : ExtensionClass K F) (p : IsoClass i F K c),
        (ξ + η) +ᵥ p = ξ +ᵥ (η +ᵥ p)) ∧
      (∀ p : IsoClass i F K c, (0 : ExtensionClass K F) +ᵥ p = p) := by
    sorry
  exact { add_vadd := laws.1, zero_vadd := laws.2 }

/-- The Baer-sum action computes on representatives. -/
theorem vadd_mk (S : Extension K F) (E : InfinitesimalExtension i F K c) :
    (⟦S⟧ : ExtensionClass K F) +ᵥ IsoClass.mk E = IsoClass.mk (vaddExt S E) := sorry

/-- Torsor subtraction computes on representatives. -/
theorem vsub_mk (E₁ E₂ : InfinitesimalExtension i F K c) :
    IsoClass.mk E₁ -ᵥ IsoClass.mk E₂ = (⟦vsubExt E₁ E₂⟧ : ExtensionClass K F) := sorry

/-- With a chosen extension as basepoint, isomorphism classes are an additive torsor
under `𝒪_X`-extension classes. -/
@[reducible]
def addTorsor (E0 : InfinitesimalExtension i F K c) :
    AddTorsor (ExtensionClass K F) (IsoClass i F K c) := by
  have laws :
      (∀ p q : IsoClass i F K c, (p -ᵥ q : ExtensionClass K F) +ᵥ q = p) ∧
      (∀ (ξ : ExtensionClass K F) (p : IsoClass i F K c), (ξ +ᵥ p) -ᵥ p = ξ) := by
    sorry
  exact { nonempty := ⟨IsoClass.mk E0⟩, vsub_vadd' := laws.1, vadd_vsub' := laws.2 }

/-- A chosen infinitesimal extension identifies extension classes over the smaller ringed
space with isomorphism classes of infinitesimal extensions having the same infinitesimal map.
The forward map is Baer translation and the inverse is the Baer difference from the basepoint. -/
def isoClassEquiv (E0 : InfinitesimalExtension i F K c) :
    ExtensionClass K F ≃ IsoClass i F K c where
  toFun ξ := ξ +ᵥ IsoClass.mk E0
  invFun p := p -ᵥ IsoClass.mk E0
  left_inv ξ := (addTorsor E0).vadd_vsub' ξ (IsoClass.mk E0)
  right_inv p := (addTorsor E0).vsub_vadd' p (IsoClass.mk E0)

/-- The based chart sends an `𝒪_X`-extension class `ξ` to the translate of the basepoint. -/
theorem isoClassEquiv_apply (E0 : InfinitesimalExtension i F K c) (ξ : ExtensionClass K F) :
    isoClassEquiv E0 ξ = ξ +ᵥ IsoClass.mk E0 := rfl

/-- The zero extension class is sent to the class of the basepoint. -/
theorem isoClassEquiv_zero (E0 : InfinitesimalExtension i F K c) :
    isoClassEquiv E0 0 = IsoClass.mk E0 := by
  change (0 : ExtensionClass K F) +ᵥ IsoClass.mk E0 = IsoClass.mk E0
  exact zero_vadd (ExtensionClass K F) (IsoClass.mk E0)

/-- The inverse chart is torsor subtraction against the basepoint. -/
theorem isoClassEquiv_symm_apply (E0 : InfinitesimalExtension i F K c)
    (p : IsoClass i F K c) :
    (isoClassEquiv E0).symm p = p -ᵥ IsoClass.mk E0 := rfl

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
