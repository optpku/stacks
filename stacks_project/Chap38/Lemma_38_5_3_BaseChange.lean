/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.CompleteDevissage.BaseChange

/-!
# Base change of complete dévissages

This compatibility module re-exports and checks the shared explicit-choice base-change API.
-/

universe u

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

#check (AlgebraicGeometry.Scheme.Modules.CompleteDevissageOver.baseChange :
  {S S' X : Scheme.{u}} → {f : X ⟶ S} → {F : X.Modules} → {s : S} →
    [h_f : LocallyOfFiniteType f] → [h_Fqc : F.IsQuasicoherent] →
      [h_Fft : F.IsFiniteType] → (D : Scheme.Modules.CompleteDevissageOver f F s) →
        (g : S' ⟶ S) → (s' : S') → (h_point : g s' = s) →
          (ξ' : ∀ k, ((Over.pullback g).obj (D.stage k).Y).hom.fiber s') →
            (hξ' : ∀ k, IsGenericPoint (ξ' k)
              (Set.univ : Set (((Over.pullback g).obj (D.stage k).Y).hom.fiber s'))) →
              [hS' : IsAffine S'] →
                @Scheme.Modules.CompleteDevissageOver S'
                  ((Over.pullback g).obj (Over.mk f)).left
                  ((Over.pullback g).obj (Over.mk f)).hom
                  (Scheme.Modules.baseChangeModule f g F :
                    ((Over.pullback g).obj (Over.mk f)).left.Modules)
                  (@Scheme.Modules.OneStepDevissage.baseChange_locallyOfFiniteType
                    S S' (Over.mk f) g h_f)
                  (@Scheme.Modules.OneStepDevissage.baseChangeModule_isQuasicoherent
                    S S' (Over.mk f) F g h_Fqc)
                  (@Scheme.Modules.OneStepDevissage.baseChangeModule_isFiniteType
                    S S' (Over.mk f) F g h_Fft) s')
