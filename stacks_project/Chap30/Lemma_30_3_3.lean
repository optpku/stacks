module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AmpleCriterion
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

universe u

/- Lemma 30.3.3: let `X` be a quasi-compact scheme and let `L` be an invertible
`𝒪_X`-module. If every quasi-coherent ideal subobject `I` has a positive tensor twist
`I.toModule ⊗ RingedSpace.TensorPower.sheaf L n` with vanishing first cohomology, then `L` is
ample. -/
@[stacks 0B5P] #check
  (AlgebraicGeometry.Scheme.Modules.isAmple_of_H1_vanishes_for_quasiCoherent_idealSheaf_tensorPowers :
    ∀ {X : Scheme.{u}} [CompactSpace X.carrier]
      (L : X.Modules) [AlgebraicGeometry.Scheme.Modules.Invertible L],
      (∀ I : Scheme.IdealSubobject X, I.toModule.IsQuasicoherent →
        ∃ n : ℕ, 0 < n ∧
          IsZero
            (((SheafOfModules.toSheaf X.ringCatSheaf).obj
              (I.toModule ⊗ RingedSpace.TensorPower.sheaf L n)).H' 1 (⊤ : X.Opens))) →
        AlgebraicGeometry.Scheme.Modules.IsAmple L)
