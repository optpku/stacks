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

/- Proposition 29.27.1 (Generic flatness): a finite-type morphism to an integral scheme and a
finite-type quasicoherent module admit a dense open on which the restricted morphism and module
are flat and of finite presentation. -/
@[stacks 052A] #check
  (AlgebraicGeometry.Scheme.Modules.exists_dense_open_genericFlatness :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsIntegral S] [Scheme.Hom.FiniteType f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType],
      ∃ U : S.Opens, Dense (U : Set S) ∧
        AlgebraicGeometry.Scheme.Modules.GenericFlatnessOn f ℱ U)
