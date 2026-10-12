/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.Eta.Tensor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Ideal.RegularPrincipal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry.RingedSpace

/- Lemma 20.55.9 (0F9W): for an action-monic complex `K` and an invertible module `L`,
`η[I] (K ⊗ L)` is canonically isomorphic to `η[I] K ⊗ L`. -/
@[stacks 0F9W]
#check @IdealSheaf.Eta.Tensor.isoApp

@[stacks 0F9W "natural flat tensor comparison"]
#check @IdealSheaf.Eta.Tensor.comparison

@[stacks 0F9W "flat complex comparison"]
#check @IdealSheaf.Eta.Tensor.complexIso

#check @IdealSheaf.Eta.Tensor.domainFunctor
#check @IdealSheaf.Eta.Tensor.complexFunctor
#check @SheafOfModules.RingedSite.IdealSheaf.IsActionMono.tensorRight
#check @SheafOfModules.RingedSite.IdealSheaf.IsActionMono.Complex.tensorRight
#check @CategoryTheory.MonoidalCategory.isFlat_of_isInvertibleObject
#check @IdealSheaf.IsRegularPrincipal.isInvertible
