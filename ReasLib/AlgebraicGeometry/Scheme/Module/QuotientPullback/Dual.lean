module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import ReasLib.Algebra.Module.ProjectiveFactorIdeal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.Quotient.Module
public import ReasLib.AlgebraicGeometry.Scheme.Blowup.Basic
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal
public import ReasLib.AlgebraicGeometry.Scheme.Module.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Monoidal
public import ReasLib.CategoryTheory.Monoidal.Closed.LaxMonoidal
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory TopologicalSpace
open CategoryTheory.MonoidalClosed
open CategoryTheory.Functor
open CategoryTheory.Functor.LaxMonoidal
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules.QuotientPullback

/-- Pullback of quotient modules to a scheme over the corresponding affine spectrum. -/
abbrev functor
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) (n : ℕ) :
    ModuleCat.{u} (A ⧸ I ^ n) ⥤ X.Modules :=
  ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n)) ⋙
    tilde.functor (CommRingCat.of A) ⋙ Scheme.Modules.pullback p

/-- The canonical comparison is the composite of the restriction, affine tilde, and pullback
internal-Hom comparisons. -/
noncomputable def comparison
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) {n : ℕ}
    (M : ModuleCat.{u} (A ⧸ I ^ n)) :
    (functor I p n).obj ((ihom M).obj (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n)))) ⟶
      (ihom ((functor I p n).obj M)).obj
        ((functor I p n).obj (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n)))) :=
  let restrict := ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))
  let restricted := InternalHom.comparison restrict M
    (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n)))
  let affine := tilde.map restricted ≫
    @tilde.InternalHom.comparison (CommRingCat.of A) (restrict.obj M)
      (restrict.obj (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n))))
  (Scheme.Modules.pullback p).map affine ≫
    @InternalHom.comparison _ _ _ _ _ _
      (Scheme.Modules.pullback p) (Scheme.Modules.pullbackMonoidal p).toLaxMonoidal
      ((tilde.functor (CommRingCat.of A)).obj
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj M))
      ((tilde.functor (CommRingCat.of A)).obj
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).obj
          (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n))))) _ _

/-- The quotient-pullback comparison is contravariantly natural in the module. -/
theorem comparison_naturality
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) {n : ℕ}
    (M N : ModuleCat.{u} (A ⧸ I ^ n)) (f : M ⟶ N) :
    (functor I p n).map
          ((MonoidalClosed.pre f).app (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n)))) ≫
        comparison I p M =
      comparison I p N ≫
        (MonoidalClosed.pre ((functor I p n).map f)).app
          ((functor I p n).obj (𝟙_ (ModuleCat.{u} (A ⧸ I ^ n)))) := sorry

/-- The quotient-pullback comparison is invertible on finite free modules. -/
noncomputable instance comparison_isIso_of_free
    {A : Type u} [CommRing A] (I : Ideal A) {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of A)) {n : ℕ}
    (M : ModuleCat.{u} (A ⧸ I ^ n)) [Module.Free (A ⧸ I ^ n) M]
    [Module.Finite (A ⧸ I ^ n) M] :
    IsIso (comparison I p M) := sorry

/-- The kernel of the comparison is annihilated by the indicated power of the pulled-back ideal
for modules whose scalar action factors through a finite free module. -/
theorem comparison_kernel_isAnnihilated
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] {n c : ℕ} (hcn : c ≤ n)
    (M : ModuleCat.{u} (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M) :
    SheafOfModules.RingedSite.IdealSheaf.IsAnnihilated
      (C := TopologicalSpace.Opens X.toRingedSpace.toPresheafedSpace)
      (J := _root_.Opens.grothendieckTopology X.toRingedSpace.toPresheafedSpace)
      (O := X.toRingedSpace.sheaf)
      (((Scheme.idealSheafDataOfIdealOnSpec I).comap p) ^ c).toSubobject
      (kernel (Scheme.Modules.toRingedSpaceMap X (comparison I p M)) :
        X.toRingedSpace.Modules) := sorry

/-- The cokernel of the comparison is annihilated by the indicated power of the pulled-back ideal
for modules whose scalar action factors through a finite free module. -/
theorem comparison_cokernel_isAnnihilated
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of A))
    [IsBlowup p (Scheme.idealSheafDataOfIdealOnSpec I)] {n c : ℕ} (hcn : c ≤ n)
    (M : ModuleCat.{u} (A ⧸ I ^ n)) [Module.Finite (A ⧸ I ^ n) M]
    (hM : Module.IsIdealProjective
      (Ideal.map (Ideal.Quotient.mk (I ^ n)) (I ^ c)) M) :
    SheafOfModules.RingedSite.IdealSheaf.IsAnnihilated
      (C := TopologicalSpace.Opens X.toRingedSpace.toPresheafedSpace)
      (J := _root_.Opens.grothendieckTopology X.toRingedSpace.toPresheafedSpace)
      (O := X.toRingedSpace.sheaf)
      (((Scheme.idealSheafDataOfIdealOnSpec I).comap p) ^ c).toSubobject
      (cokernel (Scheme.Modules.toRingedSpaceMap X (comparison I p M)) :
        X.toRingedSpace.Modules) := sorry

end AlgebraicGeometry.Scheme.Modules.QuotientPullback
