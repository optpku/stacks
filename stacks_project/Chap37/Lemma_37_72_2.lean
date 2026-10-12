/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Vanishing
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

universe u

/- Lemma 37.72.2: if `f : X ⟶ Y` is proper, the fibre over `y` has dimension at most one,
and `H¹(X_y, 𝒪_{X_y})` vanishes, then on some open neighbourhood `V` of `y` the restriction
of `R¹ f_* 𝒪_X` vanishes, as does `R¹ f'_* 𝒪_{X'}` after every cartesian base change of
`f ∣_ V`. -/
@[stacks 0E7G] #check
  (AlgebraicGeometry.Scheme.HigherDirectImage.exists_open_structureSheaf_degreeOne_isZero :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (y : Y),
      topologicalKrullDim (f.fiber y) ≤ (1 : WithBot ℕ∞) →
      IsZero (Scheme.Modules.cohomology
        (SheafOfModules.unit (f.fiber y).ringCatSheaf) 1) →
      ∃ V : Y.Opens, y ∈ V ∧
        IsZero
          ((RingedSpace.Hom.higherDirectImageModule f.toShHom
            (SheafOfModules.unit X.ringCatSheaf) 1).over V) ∧
        ∀ {X' Y' : Scheme.{u}}
          (g' : X' ⟶ (f ⁻¹ᵁ V).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ V),
          IsPullback g' f' (f ∣_ V) g →
            IsZero
              (RingedSpace.Hom.higherDirectImageModule f'.toShHom
                (SheafOfModules.unit X'.ringCatSheaf) 1))
