/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap60.Situation_60_7_5
public import stacks_project.Chap60.«60_8_1_1»
public import stacks_project.Chap60.«60_8_1_2_CrystallineObject»
public import Mathlib.AlgebraicGeometry.Over
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import ReasLib.RingTheory.Localization.AtPrime.Int
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- The base map records the scheme, closed-fibre, and ideal data used by the
   objectwise crystalline construction. -/
/-- A morphism of the divided-power setup over `Spec (ℤ_(p))`, with its map on
the closed fibres and the canonical ideal inclusion. -/
structure DividedPowerSchemeHom {p : ℕ} [Fact (Nat.Prime p)]
    {S S' : Scheme.{u}} (I : S.IdealSheafData) (I' : S'.IdealSheafData)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))) where
  /-- The underlying morphism of schemes. -/
  base : S ⟶ S'
  /-- The induced morphism of the closed fibres. -/
  zeroFiberMap : I.subscheme ⟶ I'.subscheme
  /-- Compatibility with the closed-fibre immersions. -/
  zeroFiber_comm : zeroFiberMap ≫ I'.subschemeι = I.subschemeι ≫ base
  /-- Compatibility of the structure morphisms to `Spec (ℤ_(p))`. -/
  base_over : base ≫ s' = s
  /-- Pullback of the target divided-power ideal is contained in the source ideal. -/
  ideal_compatible : I'.comap base ≤ I

namespace DividedPowerSchemeHom

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' : Scheme.{u}} {I : S.IdealSheafData} {I' : S'.IdealSheafData}
variable {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
variable {s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}

/-- Construct a setup morphism from its explicit maps and compatibility laws. -/
def of (base : S ⟶ S') (zeroFiberMap : I.subscheme ⟶ I'.subscheme)
    (zeroFiber_comm : zeroFiberMap ≫ I'.subschemeι = I.subschemeι ≫ base)
    (base_over : base ≫ s' = s) (ideal_compatible : I'.comap base ≤ I) :
    DividedPowerSchemeHom I I' s s' where
  base := base
  zeroFiberMap := zeroFiberMap
  zeroFiber_comm := zeroFiber_comm
  base_over := base_over
  ideal_compatible := ideal_compatible

/-- The setup morphism exposes its ideal compatibility condition. -/
theorem ideal_compatible_spec (g : DividedPowerSchemeHom I I' s s') :
    I'.comap g.base ≤ I := sorry

/-- The setup morphism exposes its closed-fibre, base, and ideal compatibility conditions. -/
theorem spec (g : DividedPowerSchemeHom I I' s s') :
    (g.zeroFiberMap ≫ I'.subschemeι = I.subschemeι ≫ g.base ∧
      g.base ≫ s' = s) ∧ I'.comap g.base ≤ I := sorry

end DividedPowerSchemeHom

section Functoriality

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' : Scheme.{u}} (I : S.IdealSheafData) (I' : S'.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
variable (h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (h'_compatible :
  ∀ (V : S'.affineOpens) (f : Γ(S', V)),
    (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen f))
      (S'.presheaf.map (homOfLE (S'.basicOpen_le f)).op).hom)
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable {X Y : Scheme.{u}} (x₀ : X ⟶ I.subscheme) (y₀ : Y ⟶ I'.subscheme)
variable (f : X ⟶ Y)
variable (g : DividedPowerSchemeHom I I' s s')
variable (h_comm : f ≫ y₀ = x₀ ≫ g.zeroFiberMap)

/-- The concrete crystalline-site data attached to a commutative square. -/
structure CrystallineFunctor
    {p : ℕ} [Fact (Nat.Prime p)] {S S' : Scheme.{u}}
    (I : S.IdealSheafData) (I' : S'.IdealSheafData)
    (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (h'_compatible :
      ∀ (V : S'.affineOpens) (f : Γ(S', V)),
        (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen f))
          (S'.presheaf.map (homOfLE (S'.basicOpen_le f)).op).hom)
    (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    {X Y : Scheme.{u}} (x₀ : X ⟶ I.subscheme) (y₀ : Y ⟶ I'.subscheme)
    (f : X ⟶ Y) (g : DividedPowerSchemeHom I I' s s')
    (h_comm : f ≫ y₀ = x₀ ≫ g.zeroFiberMap) where
  /-- Local nilpotence of `p` on the source. -/
  pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))
  /-- Local nilpotence of `p` on the target. -/
  pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U))
  /-- Sectionwise compatibility of the two divided-power setups. -/
  dividedPowers_compatible :
    ∀ (V : S'.affineOpens) (W : S.affineOpens)
      (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
      (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom
  /-- The concrete object assignment. -/
  obj : CRIS S I γ h_compatible X x₀ → CRIS S' I' γ' h'_compatible Y y₀
  /-- Relative crystalline objects remain compatible with the target base
  divided powers; a raw functor alone cannot supply this property. -/
  preservesBaseCompatible : ∀ A,
    CrystallineBaseCompatible I γ h_compatible x₀ A →
      CrystallineBaseCompatible I' γ' h'_compatible y₀ (obj A)
  /-- The concrete morphism assignment. -/
  map : ∀ {A B : CRIS S I γ h_compatible X x₀}, CrystallineObject.Hom A B →
    CrystallineObject.Hom (obj A) (obj B)
  /-- Preservation of identity morphisms. -/
  map_id : ∀ A : CRIS S I γ h_compatible X x₀,
    map (CrystallineObject.Hom.id A) = CrystallineObject.Hom.id (obj A)
  /-- Preservation of composition. -/
  map_comp : ∀ {A B C : CRIS S I γ h_compatible X x₀}
      (φ : CrystallineObject.Hom A B) (ψ : CrystallineObject.Hom B C),
    map (CrystallineObject.Hom.comp φ ψ) =
      CrystallineObject.Hom.comp (map φ) (map ψ)

namespace CrystallineFunctor

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S S' : Scheme.{u}} {I : S.IdealSheafData} {I' : S'.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {γ' : ∀ V : S'.affineOpens, DividedPowers (I'.ideal V)}
variable {h_compatible :
  ∀ (V : S.affineOpens) (f : Γ(S, V)),
    (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
      (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {h'_compatible :
  ∀ (V : S'.affineOpens) (f : Γ(S', V)),
    (γ' V).IsDPMorphism (γ' (S'.affineBasicOpen f))
      (S'.presheaf.map (homOfLE (S'.basicOpen_le f)).op).hom}
variable {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
variable {s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
variable {X Y : Scheme.{u}} {x₀ : X ⟶ I.subscheme} {y₀ : Y ⟶ I'.subscheme}
variable {f : X ⟶ Y} {g : DividedPowerSchemeHom I I' s s'}
variable {h_comm : f ≫ y₀ = x₀ ≫ g.zeroFiberMap}

/-- Construct the data-carrying crystalline functor from local nilpotence and
the sectionwise divided-power compatibility. -/
@[reducible] def of
    (f : X ⟶ Y) (g : DividedPowerSchemeHom I I' s s')
    (h_comm : f ≫ y₀ = x₀ ≫ g.zeroFiberMap)
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
    (dividedPowers_compatible :
      ∀ (V : S'.affineOpens) (W : S.affineOpens)
        (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
        (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom) :
    CrystallineFunctor I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g h_comm where
  pX := pX
  pY := pY
  dividedPowers_compatible := dividedPowers_compatible
  obj := fun A ↦
    { source := (Over.map f).obj A.source
      thickening := A.thickening
      thickeningToBase := A.thickeningToBase ≫ g.base
      inclusion := A.inclusion
      ideal := A.ideal
      gamma := A.gamma
      thickening_compatible := A.thickening_compatible
      isThickening := A.isThickening
      inclusion_isThickening := A.inclusion_isThickening
      ideal_eq_ker := A.ideal_eq_ker
      source_comm := sorry }
  preservesBaseCompatible := sorry
  map := fun {A B} φ ↦
    { source := (Over.map f).map φ.source
      thickening := φ.thickening
      source_comm := sorry
      base_comm := sorry
      ideal_compatible := φ.ideal_compatible
      dividedPowers_compatible := φ.dividedPowers_compatible }
  map_id := sorry
  map_comp := sorry

/-- The supplied crystalline functor exposes its local nilpotence and divided-power conditions. -/
theorem spec
    (F : CrystallineFunctor I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g h_comm) :
    ((∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) ∧
      (∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))) ∧
      (∀ (V : S'.affineOpens) (W : S.affineOpens)
        (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
        (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom) := sorry

/-- Assemble the explicit assignments into the raw crystalline-object functor. -/
def toFunctor
    (F : CrystallineFunctor I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g h_comm) :
    CRIS S I γ h_compatible X x₀ ⥤ CRIS S' I' γ' h'_compatible Y y₀ where
  obj := F.obj
  map := fun {_ _} φ ↦ F.map φ
  map_id := F.map_id
  map_comp := F.map_comp

/-- The same construction on the relative crystalline sites. -/
def toRelativeFunctor
    (F : CrystallineFunctor I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g h_comm) :
    RelativeCRIS S I γ h_compatible X x₀ ⥤
      RelativeCRIS S' I' γ' h'_compatible Y y₀ where
  obj := fun A ↦ ⟨F.obj A.1, F.preservesBaseCompatible A.1 A.2⟩
  map := fun φ ↦ F.map φ
  map_id := sorry
  map_comp := sorry

end CrystallineFunctor

end Functoriality

end AlgebraicGeometry
