module

public import Mathlib.Algebra.Torsor.Defs
public import ReasLib.CategoryTheory.Abelian.Extension.Classification
public import stacks_project.Chap91.Remark_91_4_7_Extension

/-!
# Torsor of 08L4 infinitesimal extensions

Along a first-order thickening, isomorphism classes of 08L4 extensions with a fixed
infinitesimal map form a principal homogeneous space under Baer sum with
`𝒪_X`-extension classes.  The `Ext¹` identification is the existing
`ExtensionClass.toExt` bridge, not an inverted bijection.
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

/-- The underlying mixed-scalar short exact sequence of an 08L4 extension. -/
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

/-- Two 08L4 extensions with the same infinitesimal map are equivalent when there is a
morphism between them. -/
def isoSetoid (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    Setoid (InfinitesimalExtension i F K c) where
  r E₁ E₂ := Nonempty (Hom E₁ E₂)
  iseqv := sorry

/-- Isomorphism classes of 08L4 extensions of `ℱ` by `𝒦` with infinitesimal map `c`. -/
abbrev IsoClass (i : X ⟶ X') [IsFirstOrderThickening i] (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :=
  Quotient (isoSetoid i F K c)

namespace IsoClass

/-- The isomorphism class of a given 08L4 extension. -/
def mk (E : InfinitesimalExtension i F K c) : IsoClass i F K c :=
  Quotient.mk (isoSetoid i F K c) E

/-- A morphism of 08L4 extensions identifies their isomorphism classes. -/
theorem mk_eq_mk_of_hom {E₁ E₂ : InfinitesimalExtension i F K c} (φ : Hom E₁ E₂) :
    mk E₁ = mk E₂ := sorry

end IsoClass

/-- Direct image of an `𝒪_X`-module extension along a first-order thickening. -/
def pushforwardExtension (i : X ⟶ X') [IsFirstOrderThickening i] (S : Extension K F) :
    Extension ((i _*).obj K) ((i _*).obj F) where
  E := (i _*).obj S.E
  f := (i _*).map S.f
  g := (i _*).map S.g
  zero := sorry
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

/-- The `𝒪_X`-extension obtained as the Baer difference of two 08L4 extensions with the same
`c`, after descending the middle term along `i` using that it is annihilated by `ℐ`. -/
def vsubExt (E₁ E₂ : InfinitesimalExtension i F K c) : Extension K F :=
  let D := Extension.baerSum (toExtension E₁) (Extension.neg (toExtension E₂))
  { E := (i ^*).obj D.E
    f := (asIso ((pullbackPushforwardAdjunction i).counit.app K)).inv ≫ (i ^*).map D.f
    g := (i ^*).map D.g ≫ (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom
    zero := sorry
    shortExact := sorry }

/-- Baer-sum action of an `𝒪_X`-extension class on an 08L4 isomorphism class. -/
def vadd (ξ : ExtensionClass K F) (p : IsoClass i F K c) : IsoClass i F K c :=
  _root_.Quotient.map₂ (fun S E ↦ vaddExt S E) sorry ξ p

/-- Baer difference of two 08L4 isomorphism classes, as an `𝒪_X`-extension class. -/
def vsub (p q : IsoClass i F K c) : ExtensionClass K F :=
  _root_.Quotient.map₂ (fun E₁ E₂ ↦ vsubExt E₁ E₂) sorry p q

/-- Baer sum of `𝒪_X`-extension classes acts on 08L4 isomorphism classes. -/
instance instVAdd_isoClass : VAdd (ExtensionClass K F) (IsoClass i F K c) where
  vadd := vadd

/-- Difference of 08L4 isomorphism classes is an `𝒪_X`-extension class. -/
instance instVSub_isoClass : VSub (ExtensionClass K F) (IsoClass i F K c) where
  vsub := vsub

/-- The Baer-sum action of `𝒪_X`-extension classes on 08L4 isomorphism classes. -/
instance instAddAction_isoClass : AddAction (ExtensionClass K F) (IsoClass i F K c) where
  add_vadd := sorry
  zero_vadd := sorry

/-- The Baer-sum action computes on representatives. -/
theorem vadd_mk (S : Extension K F) (E : InfinitesimalExtension i F K c) :
    (⟦S⟧ : ExtensionClass K F) +ᵥ IsoClass.mk E = IsoClass.mk (vaddExt S E) := sorry

/-- Torsor subtraction computes on representatives. -/
theorem vsub_mk (E₁ E₂ : InfinitesimalExtension i F K c) :
    IsoClass.mk E₁ -ᵥ IsoClass.mk E₂ = (⟦vsubExt E₁ E₂⟧ : ExtensionClass K F) := sorry

/-- With a chosen 08L4 extension as basepoint, isomorphism classes are an additive torsor
under `𝒪_X`-extension classes. -/
@[reducible]
def addTorsor (E0 : InfinitesimalExtension i F K c) :
    AddTorsor (ExtensionClass K F) (IsoClass i F K c) where
  nonempty := ⟨IsoClass.mk E0⟩
  vsub_vadd' := sorry
  vadd_vsub' := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
