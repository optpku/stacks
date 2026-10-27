/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Crystalline.Module
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf

universe u

namespace AlgebraicGeometry.Scheme.Crystalline

/-- The comparisons `c_φ` are epimorphisms
whenever the thickening map is a closed immersion. -/
def comparison_epi_of_closedImmersion
    (S : Scheme.{u}) (I : S.IdealSheafData)
    (γS : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
    (h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
    (X : Scheme.{u}) (x₀ : X ⟶ I.subscheme)
    (F : CrisModuleSheaf S I γS h_compatible X x₀) : Prop :=
  ∀ {T T' : smallCrystallineSite S I γS h_compatible X x₀} (φ : T ⟶ T'),
    IsClosedImmersion φ.hom.thickening → Epi (F.comparison φ)

/-- A closed immersion of thickenings induces an epimorphic comparison whenever
all closed-immersion comparisons of the coefficient are epimorphisms. -/
theorem comparison_epi_of_closedImmersion_apply
    {S : Scheme.{u}} {I : S.IdealSheafData}
    {γS : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
    {h_compatible :
      ∀ (V : S.affineOpens) (f : Γ(S, V)),
        (γS V).IsDPMorphism (γS (S.affineBasicOpen f))
          (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
    {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
    {F : CrisModuleSheaf S I γS h_compatible X x₀}
    (h : comparison_epi_of_closedImmersion S I γS h_compatible X x₀ F)
    {T T' : smallCrystallineSite S I γS h_compatible X x₀} (φ : T ⟶ T')
    (hφ : IsClosedImmersion φ.hom.thickening) :
    Epi (F.comparison φ) :=
  h φ hφ


namespace Affine

variable {A : Type u} [CommRing A] {C : Type u} [CommRing C] [Algebra A C]

/-- The ideal sheaf on `Spec A` is the one associated with `IA`. -/
def idealCompatible (IA : Ideal A) (I : (Spec.{u} (.of A)).IdealSheafData) : Prop :=
  I = Scheme.IdealSheafData.ofIdealTop
    (Ideal.comap (Scheme.ΓSpecIso (.of A)).hom.hom IA)

/-- Global divided powers on `Spec A` recover `γA` along `ΓSpecIso`. -/
def dividedPowersCompatible (IA : Ideal A) (γA : DividedPowers IA)
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (γS : ∀ V : (Spec.{u} (.of A)).affineOpens, DividedPowers (I.ideal V)) : Prop :=
  DividedPowers.IsDPMorphism γA
    (γS ⟨⊤, isAffineOpen_top (Spec (.of A))⟩)
    (Scheme.ΓSpecIso (.of A)).inv.hom

/-- The structure map of `Spec C` into the closed fibre is induced by `algebraMap A C`. -/
def structureMapCompatible
    (I : (Spec.{u} (.of A)).IdealSheafData)
    (x₀ : Spec.{u} (.of C) ⟶ I.subscheme) : Prop :=
  x₀ ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C))

/-- The structure map of `Spec C` over `V(I)` recovers `Spec.map` of `algebraMap A C`. -/
theorem structureMapCompatible.apply
    {I : (Spec.{u} (.of A)).IdealSheafData}
    {x₀ : Spec.{u} (.of C) ⟶ I.subscheme}
    (h : structureMapCompatible I x₀) :
    x₀ ≫ I.subschemeι = Spec.map (CommRingCat.ofHom (algebraMap A C)) :=
  h

/-- An ideal vanishes in a quotient presentation when its image lies in the presentation kernel. -/
theorem ideal_map_eq_bot_of_map_le_ker
    {P : Type u} [CommRing P] [Algebra A P] (IA : Ideal A)
    (π : P →ₐ[A] C) (h : Ideal.map (algebraMap A P) IA ≤ RingHom.ker π.toRingHom) :
    Ideal.map (algebraMap A C) IA = ⊥ := sorry

end Affine

end AlgebraicGeometry.Scheme.Crystalline
