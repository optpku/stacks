/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.TorAmplitude
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 36.10.6: on a quasi-separated scheme, an object of `D_QCoh(𝒪_X)` has
Tor-amplitude in `[a, b]` if and only if its derived tensor product with every
quasi-coherent `𝒪_X`-module has vanishing cohomology outside that interval. -/
@[stacks 08EA] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.hasTorAmplitudeIn_iff_homology :
    ∀ {X : Scheme.{u}} [QuasiSeparatedSpace X]
      (E : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X)
      (a b : ℤ) (hab : a ≤ b),
      RingedSpace.HasTorAmplitudeIn E.obj a b ↔
        ∀ (F : RingedSpace.QCoh X.toRingedSpace) (i : ℤ), i ∉ Set.Icc a b →
          IsZero (RingedSpace.ModuleDerived.cohomologySheaf
            (E.obj ⊗ᴸ
              (DerivedCategory.singleFunctor X.toRingedSpace.Modules 0).obj F.obj) i))

end AlgebraicGeometry.Scheme.DerivedQCoh
