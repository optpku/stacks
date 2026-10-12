/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Tangent
import StacksCheckRecall

open CategoryTheory

namespace ModuleValuedFunctor

universe u

variable {A : CommRingCat.{u}}

/- The promoted tangent decomposition is available through the compatibility import. -/
#check (tangentDecomposition :
  ∀ (F : ModuleValuedFunctor.{u, u} A) (B : Under A)
    (N : ModuleCat.{u} B.right), F.squareZeroValue B N ≅
      F.obj B ⊞ F.tangentObj B N)

/- The promoted tangent functor is available through the compatibility import. -/
#check (tangent :
  ∀ (F : ModuleValuedFunctor.{u, u} A), ModulePairFunctor A)

/- The promoted tensor-to-tangent transformation is available through the compatibility import. -/
#check (tensorToTangent :
  ∀ (F : ModuleValuedFunctor.{u, u} A),
    ModulePairFunctor.Hom F.tangentTensor F.tangent)

end ModuleValuedFunctor
