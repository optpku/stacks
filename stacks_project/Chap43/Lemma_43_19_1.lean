module

import Mathlib.Analysis.Complex.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Diagonal
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry

universe u

/- Lemma 43.19.1 (1): for coherent modules on a nonsingular variety, Tor against the
structure sheaf of the diagonal identifies with the diagonal pushforward of Tor. -/
@[stacks 0B0T] #check
  (AlgebraicGeometry.SchemeOverField.torDiagonal_isomorphic :
    ∀ (X : SchemeOverField ℂ) [Variety X] [Scheme.Regular X.left]
      (F G : X.left.Modules) [F.IsCoherent] [G.IsCoherent]
      [RingedSpace.ModuleDerived.Tensor.Has X.left.toRingedSpace]
      [RingedSpace.ModuleDerived.Tensor.Has
        (Limits.pullback X.hom X.hom).toRingedSpace] (i : ℕ),
      IsIsomorphic
        (RingedSpace.ModuleDerived.tor i
          ((Scheme.Modules.pushforward (pullback.diagonal X.hom)).obj
            (SheafOfModules.unit X.left.ringCatSheaf))
          (Scheme.Modules.externalTensorProduct X.hom X.hom F G))
        ((Scheme.Modules.pushforward (pullback.diagonal X.hom)).obj
          (RingedSpace.ModuleDerived.tor i F G)))

/- Lemma 43.19.1 (2): derived pullback along the diagonal identifies the exterior derived
tensor product of two quasicoherent complexes with their derived tensor product. -/
@[stacks 0B0T] #check
  (AlgebraicGeometry.SchemeOverField.pullbackDiagonalTensor_isomorphic :
    ∀ (X : SchemeOverField ℂ) [Variety X] [Scheme.Regular X.left]
      (K M : Scheme.DerivedQCoh X.left),
      IsIsomorphic
        ((Scheme.DerivedQCoh.pullback (pullback.diagonal X.hom)).obj
          (Scheme.DerivedQCoh.tensorObj
            ((Scheme.DerivedQCoh.pullback (pullback.fst X.hom X.hom)).obj K)
            ((Scheme.DerivedQCoh.pullback (pullback.snd X.hom X.hom)).obj M)))
        (Scheme.DerivedQCoh.tensorObj K M))

/- Lemma 43.19.1 (3): tensoring the structure sheaf of the diagonal with an exterior derived
tensor product identifies with the diagonal pushforward of the derived tensor
product. -/
@[stacks 0B0T] #check
  (AlgebraicGeometry.SchemeOverField.diagonalStructureSheafTensor_isomorphic :
    ∀ (X : SchemeOverField ℂ) [Variety X] [Scheme.Regular X.left]
      (K M : Scheme.DerivedQCoh X.left),
      IsIsomorphic
        (Scheme.DerivedQCoh.tensorObj
          (Scheme.DerivedQCoh.pushforwardStructureSheaf (pullback.diagonal X.hom))
          (Scheme.DerivedQCoh.tensorObj
            ((Scheme.DerivedQCoh.pullback (pullback.fst X.hom X.hom)).obj K)
            ((Scheme.DerivedQCoh.pullback (pullback.snd X.hom X.hom)).obj M)))
        ((Scheme.DerivedQCoh.pushforwardCohomologyIn (pullback.diagonal X.hom)).obj
          (Scheme.DerivedQCoh.tensorObj K M)))
