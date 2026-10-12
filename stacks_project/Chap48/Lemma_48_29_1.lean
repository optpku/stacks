/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.PresentationDeterminant
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry SheafOfModules
open scoped AlgebraicGeometry

universe u

/- Lemma 48.29.1: for a short exact presentation by finite locally free `𝒪_X`-modules,
the canonical determinant map is an isomorphism on the stalk at `x` exactly when its virtual
rank is nonnegative and the presented module is finite locally free of that rank near `x`. -/
@[stacks 0E9Y] #check
  (AlgebraicGeometry.LocallyRingedSpace.PresentationDeterminant.presentationMap_stalk_isIso_iff :
    ∀ {X : LocallyRingedSpace.{u}} {S : ShortComplex X.Modules}
      (hS : S.ShortExact) (r₁ r₀ : ℕ)
      [IsFiniteLocallyFreeOfRank r₁ S.X₁]
      [IsFiniteLocallyFreeOfRank r₀ S.X₂] (x : X),
      IsIso (RingedSpace.moduleStalkHom x
        (AlgebraicGeometry.LocallyRingedSpace.PresentationDeterminant.presentationMap
          hS r₁ r₀)) ↔
        r₁ ≤ r₀ ∧
          ∃ (U : TopologicalSpace.Opens X) (_ : x ∈ U),
            IsFiniteLocallyFreeOfRank (r₀ - r₁) (S.X₃.over U))
