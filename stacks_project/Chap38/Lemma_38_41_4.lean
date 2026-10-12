/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FittingIdeal.Morphism
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ModuleRestriction ZeroObject

noncomputable section

universe u

/- Lemma 38.41.4: a morphism between perfect scheme modules of Tor dimension at most one
which both vanish on a scheme-theoretically dense open `U` has, after one `U`-admissible
blowup, perfect kernel, image, and cokernel, each of Tor dimension at most one. -/
@[stacks 0ESV]
#check
  (AlgebraicGeometry.Scheme.Modules.exists_isAdmissibleBlowup_kernel_image_cokernel :
    ∀ {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens),
      SheafOfModules.IsPerfect F →
      RingedSpace.ModuleHasTorDimensionLE F 1 →
      SheafOfModules.IsPerfect G →
      RingedSpace.ModuleHasTorDimensionLE G 1 →
      schemeTheoreticallyDense U →
      IsZero (F.over U) → IsZero (G.over U) →
      ∃ (X' : Scheme.{u}) (b : X' ⟶ X),
        IsAdmissibleBlowup U b ∧
          (SheafOfModules.IsPerfect (kernel ((Scheme.Modules.pullback b).map φ)) ∧
            RingedSpace.ModuleHasTorDimensionLE
              (kernel ((Scheme.Modules.pullback b).map φ)) 1) ∧
          (SheafOfModules.IsPerfect (image ((Scheme.Modules.pullback b).map φ)) ∧
            RingedSpace.ModuleHasTorDimensionLE
              (image ((Scheme.Modules.pullback b).map φ)) 1) ∧
          (SheafOfModules.IsPerfect (cokernel ((Scheme.Modules.pullback b).map φ)) ∧
            RingedSpace.ModuleHasTorDimensionLE
              (cokernel ((Scheme.Modules.pullback b).map φ)) 1))
