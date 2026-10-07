module

public import ReasLib.AlgebraicGeometry.Scheme.Module.OneStepDevissage.BaseChange

/-!
# Base change of a one-step dévissage

This compatibility module re-exports and checks the shared base-change API.
-/

universe u

open CategoryTheory

#check (AlgebraicGeometry.Scheme.Modules.OneStepDevissage.baseChange :
  {S S' : AlgebraicGeometry.Scheme.{u}} → {X : Over S} →
    {F : X.left.Modules} → {s : S} →
      [hX : AlgebraicGeometry.LocallyOfFiniteType X.hom] →
        [hFqc : F.IsQuasicoherent] → [hFft : F.IsFiniteType] →
          AlgebraicGeometry.Scheme.Modules.OneStepDevissage X F s →
            (g : S' ⟶ S) → (s' : S') → g s' = s →
              [AlgebraicGeometry.IsAffine S'] →
                @AlgebraicGeometry.Scheme.Modules.OneStepDevissage S'
                  ((Over.pullback g).obj X)
                  (AlgebraicGeometry.Scheme.Modules.baseChangeModule X.hom g F :
                    ((Over.pullback g).obj X).left.Modules)
                  (@AlgebraicGeometry.Scheme.Modules.OneStepDevissage.baseChange_locallyOfFiniteType
                    S S' X g hX)
                  (@AlgebraicGeometry.Scheme.Modules.OneStepDevissage.baseChangeModule_isQuasicoherent
                    S S' X F g hFqc)
                  (@AlgebraicGeometry.Scheme.Modules.OneStepDevissage.baseChangeModule_isFiniteType
                    S S' X F g hFft) s')
