/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Blowup.AlmostExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open SheafOfModules.RingedSite SheafOfModules.RingedSite.IdealSheaf
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.IsBlowup

/- Lemma 51.22.2: for a short exact sequence over `A ⧸ I ^ n` whose final term is
finite and projective relative to `I ^ c ⧸ I ^ n`, the kernel of the induced map after
pullback to the blowup is annihilated by the `c`-th power of the pulled-back center ideal. -/
@[stacks 0GA8]
#check (AlgebraicGeometry.IsBlowup.kernelPullback_isAnnihilated :
    ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)]
    {n c : ℕ} (hcn : c ≤ n) (S : ShortComplex (ModuleCat (A ⧸ I ^ n)))
    (hS : S.ShortExact) [Module.Finite (A ⧸ I ^ n) S.X₃]
    (hM : Module.IsIdealProjective
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) S.X₃),
    IsAnnihilated (J := Opens.grothendieckTopology X.toRingedSpace)
      (O := X.toRingedSpace.sheaf)
      (((Scheme.idealSheafDataOfIdealOnSpec I).comap p) ^ c).toSubobject
      (Limits.kernel (toRingedSpaceMap X
        ((affineBaseModuleAssociatedFunctor A p).map
          ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).map S.f))) :
        X.toRingedSpace.Modules))

end AlgebraicGeometry.IsBlowup
