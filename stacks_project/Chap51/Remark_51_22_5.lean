/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.QuotientPullback.Dual
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open CategoryTheory.MonoidalClosed
open CategoryTheory.Functor
open CategoryTheory.Functor.LaxMonoidal
open AlgebraicGeometry
open Scheme.Modules

noncomputable section

universe u

section

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
variable {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
variable [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] {n : ℕ}
variable (M : ModuleCat.{u} (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
variable (N : ModuleCat.{u} (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) N]
variable (f : M ⟶ N)

/- Remark 51.22.5 (1): the canonical morphism from the pullback of the quotient-module dual to
the internal-Hom dual of the pullback. -/
@[stacks 0GAB] #check
  (AlgebraicGeometry.Scheme.Modules.QuotientPullback.comparison I p M :
    (QuotientPullback.functor I p n).obj
        ((ihom M).obj (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n)))) ⟶
      (ihom ((QuotientPullback.functor I p n).obj M)).obj
        ((QuotientPullback.functor I p n).obj
          (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n)))))

/- Remark 51.22.5 (2): the canonical pullback-dual comparison is contravariantly natural in the
quotient module. -/
@[stacks 0GAB] #check
  (AlgebraicGeometry.Scheme.Modules.QuotientPullback.comparison_naturality I p M N f :
    (QuotientPullback.functor I p n).map
          ((MonoidalClosed.pre f).app (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n)))) ≫
        QuotientPullback.comparison I p M =
      QuotientPullback.comparison I p N ≫
        (MonoidalClosed.pre
          ((QuotientPullback.functor I p n).map f)).app
          ((QuotientPullback.functor I p n).obj
            (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n)))))

variable {c : ℕ} (hcn : c ≤ n)
variable (hM : Module.IsIdealProjective
  (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M)

/- Remark 51.22.5 (3): for an `(A, n, c)`-module, the kernel of the canonical comparison is
annihilated by the `c`-th power of the pulled-back ideal. -/
@[stacks 0GAB] #check
  (AlgebraicGeometry.Scheme.Modules.QuotientPullback.comparison_kernel_isAnnihilated
    I p hcn M hM :
    SheafOfModules.RingedSite.IdealSheaf.IsAnnihilated
      (C := TopologicalSpace.Opens X.toRingedSpace.toPresheafedSpace)
      (J := _root_.Opens.grothendieckTopology X.toRingedSpace.toPresheafedSpace)
      (O := X.toRingedSpace.sheaf)
      (((Scheme.idealSheafDataOfIdealOnSpec I).comap p) ^ c).toSubobject
      (kernel (Scheme.Modules.toRingedSpaceMap X
        (QuotientPullback.comparison I p M)) :
        X.toRingedSpace.Modules))

/- Remark 51.22.5 (4): for an `(A, n, c)`-module, the cokernel of the canonical comparison is
annihilated by the `c`-th power of the pulled-back ideal. -/
@[stacks 0GAB] #check
  (AlgebraicGeometry.Scheme.Modules.QuotientPullback.comparison_cokernel_isAnnihilated
    I p hcn M hM :
    SheafOfModules.RingedSite.IdealSheaf.IsAnnihilated
      (C := TopologicalSpace.Opens X.toRingedSpace.toPresheafedSpace)
      (J := _root_.Opens.grothendieckTopology X.toRingedSpace.toPresheafedSpace)
      (O := X.toRingedSpace.sheaf)
      (((Scheme.idealSheafDataOfIdealOnSpec I).comap p) ^ c).toSubobject
      (cokernel (Scheme.Modules.toRingedSpaceMap X
        (QuotientPullback.comparison I p M)) :
        X.toRingedSpace.Modules))

end
