module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.AffineBaseChange
public import ReasLib.AlgebraicGeometry.Scheme.HigherDirectImage.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 30.5.1: for an affine morphism `f : X ⟶ S`, pushforward of a quasi-coherent
module agrees with derived pushforward, remains quasi-coherent, and commutes with arbitrary
cartesian base change. -/
@[stacks 02KG] #check
  (AlgebraicGeometry.Scheme.affineBaseChange_pushforward_isomorphic :
    ∀ {X X' S S' : AlgebraicGeometry.Scheme.{u}}
      (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
      (sq : IsPullback g' f' f g) [AlgebraicGeometry.IsAffineHom f]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
        IsIsomorphic
          (((AlgebraicGeometry.Scheme.Modules.pullback g).obj
            ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ)) : S'.Modules)
          (((AlgebraicGeometry.Scheme.Modules.pushforward f').obj
            ((AlgebraicGeometry.Scheme.Modules.pullback g').obj ℱ)) : S'.Modules))

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)

section

variable [CategoryTheory.HasInjectiveResolutions X.Modules]

#check
  (CategoryTheory.Functor.rightDerivedZeroIsoSelf
      (F := AlgebraicGeometry.Scheme.Modules.pushforward f) :
    (AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived 0 ≅
      AlgebraicGeometry.Scheme.Modules.pushforward f)

end

#check
  (AlgebraicGeometry.Scheme.higherDirectImageModule_isZero_of_isAffineHom :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.IsAffineHom f]
      [CategoryTheory.HasInjectiveResolutions X.Modules]
      (ℱ : X.Modules) [ℱ.IsQuasicoherent] (i : ℕ), 0 < i →
        IsZero
          (((AlgebraicGeometry.Scheme.Modules.pushforward f).rightDerived i).obj ℱ))

section

variable [AlgebraicGeometry.IsAffineHom f]

#check
  (AlgebraicGeometry.Scheme.Modules.pushforward.isQuasicoherent f :
    ∀ (ℱ : X.Modules) [ℱ.IsQuasicoherent],
      ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj ℱ).IsQuasicoherent)

end
