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
    ∀ {X : Scheme.{u}} {F G : X.Modules}
      [sourceTensor : DerivedCategory.DerivedTensor.Right.Has
        (C := RingedSpace.Modules X.toRingedSpace)]
      (φ : F ⟶ G) (U : X.Opens)
      (hPerfectF : SheafOfModules.IsPerfect F)
      (hTorF : RingedSpace.ModuleHasTorDimensionLE F 1)
      (hPerfectG : SheafOfModules.IsPerfect G)
      (hTorG : RingedSpace.ModuleHasTorDimensionLE G 1)
      (hDense : schemeTheoreticallyDense U)
      (hZeroF : IsZero (F.over U)) (hZeroG : IsZero (G.over U))
      (tensorOnBlowups : ∀ {X' : Scheme.{u}} (b : X' ⟶ X),
        IsAdmissibleBlowup U b →
          DerivedCategory.DerivedTensor.Right.Has
            (C := RingedSpace.Modules X'.toRingedSpace)),
      ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (hb : IsAdmissibleBlowup U b),
        letI := tensorOnBlowups b hb
        (SheafOfModules.IsPerfect (kernel ((Scheme.Modules.pullback b).map φ)) ∧
          RingedSpace.ModuleHasTorDimensionLE
            (kernel ((Scheme.Modules.pullback b).map φ)) 1) ∧
        (SheafOfModules.IsPerfect (image ((Scheme.Modules.pullback b).map φ)) ∧
          RingedSpace.ModuleHasTorDimensionLE
            (image ((Scheme.Modules.pullback b).map φ)) 1) ∧
        (SheafOfModules.IsPerfect (cokernel ((Scheme.Modules.pullback b).map φ)) ∧
          RingedSpace.ModuleHasTorDimensionLE
            (cokernel ((Scheme.Modules.pullback b).map φ)) 1))
