module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.PresentationDeterminant
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory
open AlgebraicGeometry SheafOfModules
open scoped AlgebraicGeometry

universe u

/- Lemma 48.29.1: for a short exact presentation by finite locally free `𝒪_X`-modules,
the canonical determinant map, expressed in the internal-Hom target, is an isomorphism on the
stalk at `x` exactly when its virtual rank is nonnegative and the presented module is finite
locally free of that rank near `x`. -/
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

/- Lemma 48.29.1 (tensor target): the internal-Hom map corresponds to a unique map into the
determinant-dual tensor target of the source. -/
#check
  (AlgebraicGeometry.LocallyRingedSpace.PresentationDeterminant.presentationMap_existsUnique_tensor :
    ∀ {X : LocallyRingedSpace.{u}} {S : ShortComplex X.Modules}
      (hS : S.ShortExact) (r₁ r₀ : ℕ)
      [IsFiniteLocallyFreeOfRank r₁ S.X₁]
      [IsFiniteLocallyFreeOfRank r₀ S.X₂],
      ∃! φ :
          AlgebraicGeometry.LocallyRingedSpace.PresentationDeterminant.presentationSource S r₁ r₀ ⟶
            (MonoidalClosed.dual (Λ[r₁] S.X₁)) ⊗ (Λ[r₀] S.X₂),
        φ ≫ (β_ (Λ[r₀] S.X₂) (MonoidalClosed.dual (Λ[r₁] S.X₁))).inv ≫
          MonoidalClosed.Dual.tensorComparison (Λ[r₁] S.X₁) (Λ[r₀] S.X₂) =
            AlgebraicGeometry.LocallyRingedSpace.PresentationDeterminant.presentationMap hS r₁ r₀)
