module

public import stacks_project.Chap60.Lemma_60_15_1_Connection
public import stacks_project.Chap60.Remark_60_6_8_Connection
import Mathlib.Tactic.CrossRefAttribute

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Crystalline
open CrystallineModuleSheaf
open CrisModuleSheaf
open scoped TensorProduct

@[expose] public section

universe u

variable {p : ℕ} [Fact (Nat.Prime p)]
variable {S : Scheme.{u}} {I : S.IdealSheafData}
variable {γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V)}
variable {h_compatible :
    ∀ (V : S.affineOpens) (f : Γ(S, V)),
      (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
        (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom}
variable {s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p)))}
variable {X : Scheme.{u}} {x₀ : X ⟶ I.subscheme}
variable {h_p : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U))}

/-- Lemma 60.15.1: In Situation 60.7.5, a crystal `F` in `𝒪_{X/S}`-modules on
`Cris(X/S)` carries a canonical integrable connection, obtained objectwise from the
first-order square-zero thickening of Remark 60.13.1 and checked integrable via the
second-order thickening of Remark 60.13.2. -/
@[stacks 07J6]
theorem canonicalConnection_isIntegrable
    (F : CrisModuleSheaf S I γ h_compatible X x₀) [CrisModuleSheaf.IsCrystal F]
    (T : smallCrystallineSite S I γ h_compatible X x₀) :
    Connection.IsIntegrable (canonicalConnection F T) (exteriorCalculus T) := sorry

end
