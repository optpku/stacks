/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Base
public import ReasLib.AlgebraicGeometry.Crystalline.Object
public import ReasLib.AlgebraicGeometry.Crystalline.Site
public import ReasLib.CategoryTheory.Sites.Topos.Continuous
public import ReasLib.CategoryTheory.Sites.Topos.Cocontinuous

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
    I'.comap g.base ≤ I := g.ideal_compatible

/-- The setup morphism exposes its closed-fibre, base, and ideal compatibility conditions. -/
theorem spec (g : DividedPowerSchemeHom I I' s s') :
    (g.zeroFiberMap ≫ I'.subschemeι = I.subschemeι ≫ g.base ∧
      g.base ≫ s' = s) ∧ I'.comap g.base ≤ I :=
  ⟨⟨g.zeroFiber_comm, g.base_over⟩, g.ideal_compatible⟩

end DividedPowerSchemeHom

namespace Scheme.Crystalline

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
variable {X Y : Scheme.{u}} {x₀ : X ⟶ I.subscheme} {y₀ : Y ⟶ I'.subscheme}

variable (f : X ⟶ Y) (base : S ⟶ S')
variable (zeroFiberMap : I.subscheme ⟶ I'.subscheme)
variable (zeroFiber_comm : zeroFiberMap ≫ I'.subschemeι = I.subschemeι ≫ base)
variable (h_comm : f ≫ y₀ = x₀ ≫ zeroFiberMap)

include zeroFiberMap zeroFiber_comm h_comm in
/-- Composing the structural maps of a crystalline object preserves its structural square. -/
theorem mapObject_source_comm (A : CRIS S I γ h_compatible X x₀) :
    A.inclusion ≫ (A.thickeningToBase ≫ base) =
      ((Over.map f).obj A.source).hom ≫ y₀ ≫ I'.subschemeι := sorry

variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (base_over : base ≫ s' = s) (ideal_compatible : I'.comap base ≤ I)
variable (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
variable (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))

variable (dividedPowers_compatible :
  ∀ (V : S'.affineOpens) (W : S.affineOpens)
    (hVW : W.1 ≤ base ⁻¹ᵁ V.1),
    (γ' V).IsDPMorphism (γ W) (base.appLE V W hVW).hom)

/-- Change the source and base maps of a crystalline object without changing its thickening.
The prime-local and divided-power hypotheses specify the relative change-of-base construction. -/
def mapObject (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (base_over : base ≫ s' = s) (ideal_compatible : I'.comap base ≤ I)
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
    (dividedPowers_compatible :
      ∀ (V : S'.affineOpens) (W : S.affineOpens)
        (hVW : W.1 ≤ base ⁻¹ᵁ V.1),
        (γ' V).IsDPMorphism (γ W) (base.appLE V W hVW).hom)
    (A : CRIS S I γ h_compatible X x₀) :
    CRIS S' I' γ' h'_compatible Y y₀ where
  source := (Over.map f).obj A.source
  thickening := A.thickening
  thickeningToBase := A.thickeningToBase ≫ base
  inclusion := A.inclusion
  ideal := A.ideal
  gamma := A.gamma
  thickening_compatible := A.thickening_compatible
  isThickening := A.isThickening
  inclusion_isThickening := A.inclusion_isThickening
  ideal_eq_ker := A.ideal_eq_ker
  source_comm := mapObject_source_comm f base zeroFiberMap zeroFiber_comm h_comm A

/-- Change of base preserves the source scheme over the new target. -/
@[simp] theorem mapObject_source (A : CRIS S I γ h_compatible X x₀) :
    (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) A).source =
      (Over.map f).obj A.source := rfl

/-- Change of base leaves the thickening scheme unchanged. -/
@[simp] theorem mapObject_thickening (A : CRIS S I γ h_compatible X x₀) :
    (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) A).thickening =
      A.thickening := rfl

/-- Change of base leaves the thickening ideal unchanged. -/
@[simp] theorem mapObject_ideal (A : CRIS S I γ h_compatible X x₀) :
    (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) A).ideal =
      A.ideal := rfl

/-- Change of base leaves the divided powers on the thickening unchanged. -/
@[simp] theorem mapObject_gamma (A : CRIS S I γ h_compatible X x₀) :
    (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) A).gamma =
      A.gamma := rfl

/-- A divided-power-compatible base map preserves relative crystalline objects. -/
theorem mapObject_baseCompatible (A : CRIS S I γ h_compatible X x₀)
    (hA : CrystallineBaseCompatible I γ h_compatible x₀ A) :
    CrystallineBaseCompatible I' γ' h'_compatible y₀
      (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible A) := sorry

/-- The unchanged maps of a crystalline morphism still commute with the source inclusions. -/
theorem mapHom_source_comm {A B : CRIS S I γ h_compatible X x₀}
    (φ : CrystallineObject.Hom A B) :
    ((Over.map f).map φ.source).left ≫
        (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) B).inclusion =
      (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) A).inclusion ≫
        φ.thickening := sorry

/-- The unchanged thickening map commutes with the composed base maps. -/
theorem mapHom_base_comm {A B : CRIS S I γ h_compatible X x₀}
    (φ : CrystallineObject.Hom A B) :
    φ.thickening ≫ (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) B).thickeningToBase =
      (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) A).thickeningToBase := sorry

/-- Change of base keeps the underlying source and thickening maps of a crystalline morphism. -/
def mapHom {A B : CRIS S I γ h_compatible X x₀}
    (φ : CrystallineObject.Hom A B) :
    CrystallineObject.Hom (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) A) (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible B) where
  source := (Over.map f).map φ.source
  thickening := φ.thickening
  source_comm := mapHom_source_comm f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible φ
  base_comm := mapHom_base_comm f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible φ
  ideal_compatible := φ.ideal_compatible
  dividedPowers_compatible := φ.dividedPowers_compatible

/-- Change of base preserves identity crystalline morphisms. -/
theorem mapFunctor_map_id (A : CRIS S I γ h_compatible X x₀) :
    mapHom f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) (CrystallineObject.Hom.id A) =
      CrystallineObject.Hom.id (mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible A) := sorry

/-- Change of base preserves composition of crystalline morphisms. -/
theorem mapFunctor_map_comp {A B C : CRIS S I γ h_compatible X x₀}
    (φ : CrystallineObject.Hom A B) (ψ : CrystallineObject.Hom B C) :
    mapHom f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible
        (γ' := γ') (h'_compatible := h'_compatible) (CrystallineObject.Hom.comp φ ψ) =
      CrystallineObject.Hom.comp (mapHom f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible φ) (mapHom f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible ψ) := sorry

/-- A prime-local divided-power base morphism induces the objectwise functor of relative crystalline sites. -/
@[reducible] def mapFunctor (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (s' : S' ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
    (base_over : base ≫ s' = s) (ideal_compatible : I'.comap base ≤ I)
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U))) :
    RelativeCRIS S I γ h_compatible X x₀ ⥤ RelativeCRIS S' I' γ' h'_compatible Y y₀ where
  obj := fun A ↦ ⟨mapObject f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible A.1,
    mapObject_baseCompatible f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible A.1 A.2⟩
  map := fun φ ↦ mapHom f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible φ
  map_id := fun A ↦ mapFunctor_map_id f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible A.1
  map_comp := fun φ ψ ↦ mapFunctor_map_comp f base zeroFiberMap zeroFiber_comm h_comm
        s s' base_over ideal_compatible pX pY dividedPowers_compatible φ ψ

/-- The crystalline change-of-base functor is continuous for the crystalline Zariski topologies. -/
instance mapFunctor_isContinuous :
    (mapFunctor f base zeroFiberMap zeroFiber_comm h_comm
      dividedPowers_compatible s s' base_over ideal_compatible pX pY).IsContinuous
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) := sorry

/-- The crystalline change-of-base functor is cocontinuous for the crystalline Zariski topologies. -/
instance mapFunctor_isCocontinuous :
    (mapFunctor f base zeroFiberMap zeroFiber_comm h_comm
      dividedPowers_compatible s s' base_over ideal_compatible pX pY).IsCocontinuous
      (crystallineZariskiTopology S I γ h_compatible X x₀)
      (crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) := sorry

end Scheme.Crystalline

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
  obj := Scheme.Crystalline.mapObject f g.base g.zeroFiberMap g.zeroFiber_comm h_comm
    s s' g.base_over g.ideal_compatible pX pY dividedPowers_compatible
  preservesBaseCompatible := Scheme.Crystalline.mapObject_baseCompatible f g.base g.zeroFiberMap g.zeroFiber_comm h_comm
    s s' g.base_over g.ideal_compatible pX pY dividedPowers_compatible
  map := Scheme.Crystalline.mapHom f g.base g.zeroFiberMap g.zeroFiber_comm h_comm
    s s' g.base_over g.ideal_compatible pX pY dividedPowers_compatible
  map_id := Scheme.Crystalline.mapFunctor_map_id f g.base g.zeroFiberMap g.zeroFiber_comm h_comm
    s s' g.base_over g.ideal_compatible pX pY dividedPowers_compatible
  map_comp := Scheme.Crystalline.mapFunctor_map_comp f g.base g.zeroFiberMap g.zeroFiber_comm h_comm
    s s' g.base_over g.ideal_compatible pX pY dividedPowers_compatible

/-- The supplied crystalline functor exposes its local nilpotence and divided-power conditions. -/
theorem spec
    (F : CrystallineFunctor I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g h_comm) :
    ((∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))) ∧
      (∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))) ∧
      (∀ (V : S'.affineOpens) (W : S.affineOpens)
        (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
        (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom) :=
  ⟨⟨F.pX, F.pY⟩, F.dividedPowers_compatible⟩

/-- Assemble the explicit assignments into the raw crystalline-object functor. -/
def toFunctor
    (F : CrystallineFunctor I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g h_comm) :
    CRIS S I γ h_compatible X x₀ ⥤ CRIS S' I' γ' h'_compatible Y y₀ where
  obj := F.obj
  map := fun {_ _} φ ↦ F.map φ
  map_id := F.map_id
  map_comp := F.map_comp

/-- The same construction on the relative crystalline sites. -/
@[reducible] def toRelativeFunctor
    (F : CrystallineFunctor I I' γ γ' h_compatible h'_compatible s s' x₀ y₀ f g h_comm) :
    RelativeCRIS S I γ h_compatible X x₀ ⥤
      RelativeCRIS S' I' γ' h'_compatible Y y₀ where
  obj := fun A ↦ ⟨F.obj A.1, F.preservesBaseCompatible A.1 A.2⟩
  map := fun φ ↦ F.map φ
  map_id := fun A ↦ F.map_id A.1
  map_comp := fun φ ψ ↦ F.map_comp φ ψ

end CrystallineFunctor

end Functoriality

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
variable (h_dividedPowers_compatible :
  ∀ (V : S'.affineOpens) (W : S.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (γ' V).IsDPMorphism (γ W) (g.base.appLE V W hVW).hom)

/-- The explicit crystalline construction is continuous for the crystalline Zariski topologies. -/
theorem crystallineFunctor_isContinuous
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
    : (CrystallineFunctor.of f g h_comm pX pY
      h_dividedPowers_compatible).toRelativeFunctor.IsContinuous
      (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
      (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) :=
  Scheme.Crystalline.mapFunctor_isContinuous f g.base g.zeroFiberMap g.zeroFiber_comm h_comm
    s s' g.base_over g.ideal_compatible pX pY h_dividedPowers_compatible

/-- The explicit crystalline construction is cocontinuous for the crystalline Zariski topologies. -/
theorem crystallineFunctor_isCocontinuous
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
    : (CrystallineFunctor.of f g h_comm pX pY
      h_dividedPowers_compatible).toRelativeFunctor.IsCocontinuous
      (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
      (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) :=
  Scheme.Crystalline.mapFunctor_isCocontinuous f g.base g.zeroFiberMap g.zeroFiber_comm h_comm
    s s' g.base_over g.ideal_compatible pX pY h_dividedPowers_compatible

/-- The continuous crystalline functor gives a conditional morphism from sheaves on
the target crystalline site to sheaves on the source crystalline site, when its
sheaf pullback preserves finite limits. -/
noncomputable def crystallineToposHom
    (pX : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))
    (pY : ∀ U : Y.affineOpens, IsNilpotent (p : Γ(Y, U)))
    [HasWeakSheafify
      (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀)
      (Type (u + 1))]
    [∀ P : (RelativeCRIS S I γ h_compatible X x₀)ᵒᵖ ⥤ Type (u + 1),
      (Functor.op (CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor).HasLeftKanExtension P]
    [PreservesFiniteLimits
      ((CrystallineFunctor.of f g h_comm pX pY
        h_dividedPowers_compatible).toRelativeFunctor.sheafPullback (Type (u + 1))
        (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
        (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀))] :
    MorphismOfTopoiIn
      (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
      (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀) :=
  (CrystallineFunctor.of f g h_comm pX pY
    h_dividedPowers_compatible).toRelativeFunctor.morphismOfTopoiInOfContinuous
    (Scheme.Crystalline.crystallineZariskiTopology S I γ h_compatible X x₀)
    (Scheme.Crystalline.crystallineZariskiTopology S' I' γ' h'_compatible Y y₀)

end Functoriality

namespace Scheme.Crystalline

variable {p : ℕ} [Fact (Nat.Prime p)] (B B' : Base.{u} p)
variable (f : B.source ⟶ B'.source)
variable (g : DividedPowerSchemeHom B.ideal B'.ideal B.toSpec B'.toSpec)
variable (h_comm : f ≫ B'.sourceToClosed = B.sourceToClosed ≫ g.zeroFiberMap)
variable (h_dividedPowers_compatible :
  ∀ (V : B'.scheme.affineOpens) (W : B.scheme.affineOpens)
    (hVW : W.1 ≤ g.base ⁻¹ᵁ V.1),
    (B'.dividedPowers V).IsDPMorphism (B.dividedPowers W) (g.base.appLE V W hVW).hom)

/-- A divided-power base morphism and commuting source square induce a geometric
morphism from the source crystalline topos to the target crystalline topos. -/
def functorialToposHom :
    MorphismOfTopoiIn.{u + 1, u + 1, u, u, u + 1}
      (crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.source B'.sourceToClosed)
      (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed) :=
  (mapFunctor (h_compatible := B.compatible) (h'_compatible := B'.compatible)
    f g.base g.zeroFiberMap g.zeroFiber_comm h_comm h_dividedPowers_compatible
    B.toSpec B'.toSpec g.base_over g.ideal_compatible B.prime_nilpotent B'.prime_nilpotent).morphismOfTopoiInOfCocontinuous.{u + 1, u, u, u + 1, u + 1}
    (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed)
    (crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.source B'.sourceToClosed)

/-- The inverse image of the crystalline geometric morphism is the sheafified pullback. -/
@[simp] theorem functorialToposHom_inverseImage :
    (functorialToposHom B B' f g h_comm h_dividedPowers_compatible).inverseImage =
      (mapFunctor (h_compatible := B.compatible) (h'_compatible := B'.compatible)
    f g.base g.zeroFiberMap g.zeroFiber_comm h_comm h_dividedPowers_compatible
    B.toSpec B'.toSpec g.base_over g.ideal_compatible B.prime_nilpotent B'.prime_nilpotent).sheafPullbackCocontinuous (Type (u + 1))
        (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed)
        (crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.source B'.sourceToClosed) := rfl

/-- The direct image of the crystalline geometric morphism is cocontinuous sheaf pushforward. -/
@[simp] theorem functorialToposHom_pushforward :
    (functorialToposHom B B' f g h_comm h_dividedPowers_compatible).pushforward =
      (mapFunctor (h_compatible := B.compatible) (h'_compatible := B'.compatible)
    f g.base g.zeroFiberMap g.zeroFiber_comm h_comm h_dividedPowers_compatible
    B.toSpec B'.toSpec g.base_over g.ideal_compatible B.prime_nilpotent B'.prime_nilpotent).sheafPushforwardCocontinuous (Type (u + 1))
        (crystallineZariskiTopology B.scheme B.ideal B.dividedPowers B.compatible B.source B.sourceToClosed)
        (crystallineZariskiTopology B'.scheme B'.ideal B'.dividedPowers B'.compatible B'.source B'.sourceToClosed) := rfl

end Scheme.Crystalline

end AlgebraicGeometry
