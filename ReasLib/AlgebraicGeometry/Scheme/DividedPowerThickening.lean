/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.DividedPowers.DPMorphism
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A divided-power structure on an ideal sheaf defines a divided-power thickening
when its canonical closed immersion is a scheme-theoretic thickening. -/
def IsDividedPowerThickening (T : Scheme.{u}) (J : T.IdealSheafData)
    (γ : ∀ V : T.affineOpens, DividedPowers (J.ideal V))
    (h_compatible :
      ∀ (V : T.affineOpens) (f : Γ(T, V)),
        (γ V).IsDPMorphism (γ (T.affineBasicOpen f))
          (T.presheaf.map (homOfLE (T.basicOpen_le f)).op).hom) : Prop :=
  let _ := h_compatible
  IsThickening J.subschemeι

/-- The divided-power thickening condition is equivalent to the thickening property
of the canonical closed immersion. -/
theorem isDividedPowerThickening_iff (T : Scheme.{u}) (J : T.IdealSheafData)
    (γ : ∀ V : T.affineOpens, DividedPowers (J.ideal V))
    (h_compatible :
      ∀ (V : T.affineOpens) (f : Γ(T, V)),
        (γ V).IsDPMorphism (γ (T.affineBasicOpen f))
          (T.presheaf.map (homOfLE (T.basicOpen_le f)).op).hom) :
    IsDividedPowerThickening T J γ h_compatible ↔ IsThickening J.subschemeι := sorry

/-- A divided power scheme with a quasi-coherent ideal sheaf is a divided power
thickening when its canonical closed immersion is a scheme-theoretic thickening. -/
def IsDividedPowerSchemeThickening (T : Scheme.{u}) (J : T.IdealSheafData)
    (h_quasiCoherent : J.toModule.IsQuasicoherent)
    (γ : ∀ V : T.affineOpens, DividedPowers (J.ideal V))
    (h_compatible :
      ∀ (V : T.affineOpens) (f : Γ(T, V)),
        (γ V).IsDPMorphism (γ (T.affineBasicOpen f))
          (T.presheaf.map (homOfLE (T.basicOpen_le f)).op).hom) : Prop :=
  let _ := h_quasiCoherent
  let _ := h_compatible
  IsThickening J.subschemeι

/-- For a divided power scheme with a quasi-coherent ideal sheaf, being a divided
power thickening is equivalent to the thickening property of its canonical closed immersion. -/
theorem isDividedPowerSchemeThickening_iff (T : Scheme.{u}) (J : T.IdealSheafData)
    (h_quasiCoherent : J.toModule.IsQuasicoherent)
    (γ : ∀ V : T.affineOpens, DividedPowers (J.ideal V))
    (h_compatible :
      ∀ (V : T.affineOpens) (f : Γ(T, V)),
        (γ V).IsDPMorphism (γ (T.affineBasicOpen f))
          (T.presheaf.map (homOfLE (T.basicOpen_le f)).op).hom) :
    IsDividedPowerSchemeThickening T J h_quasiCoherent γ h_compatible ↔
      IsThickening J.subschemeι := sorry

end AlgebraicGeometry
