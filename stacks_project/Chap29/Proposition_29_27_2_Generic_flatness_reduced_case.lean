/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.GenericFlatness
import StacksCheckRecall

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Proposition 29.27.2 (Generic flatness, reduced case): a finite-type morphism to a reduced
scheme and a finite-type quasicoherent module admit a dense open on which the restricted morphism
and module are flat and of finite presentation. -/
@[stacks 052B] #check
  (AlgebraicGeometry.Scheme.Modules.exists_dense_open_genericFlatness_of_reduced :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsReduced S] [Scheme.Hom.FiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType],
      ∃ U : S.Opens, Dense (U : Set S) ∧
        AlgebraicGeometry.Scheme.Modules.GenericFlatnessOn f ℱ U)
