/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.MaximalDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.Support
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/- Lemma 48.22.3 (1) -/
@[stacks 0AWK] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule.support_eq_maximalDimensionComponentSupport :
    ∀ {X : Scheme.{u}} [h_noetherian : IsNoetherian X] [h_connected : ConnectedSpace X]
      [h_monoidal : MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (K : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) (ωX : X.Modules)
      (hω : AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule K H n ωX)
      (δ : X → ℤ) [h_dimension : IsDimensionFunction δ],
      RingedSpace.moduleSupport ωX = Scheme.maximalDimensionComponentSupport X δ)

/- Lemma 48.22.3 (2) -/
@[stacks 0AWK] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule.coherent_of :
    ∀ {X : Scheme.{u}} (K : RingedSpace.ModuleDerived X.toRingedSpace)
      [h_monoidal : MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace)) (n : ℤ) (M : X.Modules),
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule K H n M → M.IsCoherent)

/- Lemma 48.22.3 (3) -/
@[stacks 0AWK] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule.satisfiesSerreConditionSTwo :
    ∀ {X : Scheme.{u}} [h_noetherian : IsNoetherian X] [h_connected : ConnectedSpace X]
      [h_monoidal : MonoidalCategory (RingedSpace.ModuleDerived X.toRingedSpace)]
      (H : MonoidalClosed (RingedSpace.ModuleDerived X.toRingedSpace))
      (K : RingedSpace.ModuleDerived X.toRingedSpace) (n : ℤ) (ωX : X.Modules)
      (hω : AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingModule K H n ωX),
      @Scheme.Modules.satisfiesSerreConditionS X inferInstance ωX hω.coherent 2)

end AlgebraicGeometry
