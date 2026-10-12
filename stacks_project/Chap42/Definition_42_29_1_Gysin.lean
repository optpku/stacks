/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Gysin

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {S X : Scheme.{u}} (p : X ⟶ S) [UniversallyCatenary S]
  [LocallyOfFiniteType p] (δ : S → ℤ) [IsDimensionFunction δ]
  (ℒ : X.Modules) [Invertible ℒ] (s : ℒ.sections) (k : ℤ)

/- Compatibility check for the zero-scheme Gysin homomorphism after its migration to the
reusable Chow-group owner. -/
#check (AlgebraicGeometry.Scheme.Modules.gysin p δ ℒ s k :
  CycleGroup X (p.relativeDimensionFunction δ) (k + 1) →+
    @ChowGroup (zeroScheme ℒ s)
      (@zeroSchemeIsLocallyNoetherian X (LocallyOfFiniteType.isLocallyNoetherian p)
        ℒ inferInstance s)
      ((zeroSchemeι ℒ s ≫ p).relativeDimensionFunction δ) inferInstance k)

end AlgebraicGeometry.Scheme.Modules
