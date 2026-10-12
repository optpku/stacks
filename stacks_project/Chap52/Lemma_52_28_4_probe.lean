/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap52.Lemma_52_16_2
import stacks_project.Chap52.Definition_52_16_7
import ReasLib.RingTheory.AdicCompletion.Graded
import ReasLib.CategoryTheory.InverseSystem.Positive.Sequential
import ReasLib.CategoryTheory.Abelian.SerreQuotient
import ReasLib.Algebra.Module.IdealPower.Serre
import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Completion
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.Algebra.Category.FGModuleCat.Abelian

open CategoryTheory Opposite AlgebraicGeometry
open CategoryTheory.Limits

noncomputable section
universe u v

#check AdicCompletion.Graded.Realization
#check AdicCompletion.Graded.Realization.nonempty
#check AlgebraicGeometry.AffineAlgebraizationSetup.ModuleSystem
#check AlgebraicGeometry.AffineAlgebraizationSetup.ModuleSystem.toFormalModule
#check AlgebraicGeometry.Scheme.CoherentFormalModules.CanonicallyExtends
#check AlgebraicGeometry.Scheme.CoherentCompletion.functor
#check FGModuleCat.of
#check ObjectProperty.SerreClassLocalization.quotientExactFunctor
#check CategoryTheory.PNatInverseSystem.toSequential
#check Pro.lim
#check AdicCompletion.positiveQuotientSystem
#check ModuleCat.isIdealPowerTorsion
#check DirectSum.Decomposition
#check SetLike.GradedSMul
#check (forget₂ (FGModuleCat ℤ) (ModuleCat ℤ))
#check CategoryTheory.SequentialInverseSystem.shift
#check CategoryTheory.Pro.lim
#check CategoryTheory.Functor.map
#check ModuleCat
#check @ModuleCat
#check @ModuleCat.uliftFunctor
#check CategoryTheory.ObjectProperty.isoModSerre
#check AlgebraicGeometry.AffineAlgebraizationSetup.ModuleSystem.system
#check CategoryTheory.ModuleCat.isIdealPowerTorsion
#check CategoryTheory.ObjectProperty.SerreClassLocalization.quotientExactFunctor
#check CategoryTheory.Pro.SequentialHom
#check CategoryTheory.Pro.SequentialHom.map
#check CategoryTheory.Pro.SequentialHom.isIso_toHom_iff_hasRepresentativeInverse

namespace Test
open CategoryTheory
variable {A : Type u} [CommRing A] [IsNoetherianRing A]

noncomputable def qseq (I : Ideal A) (N : Type u) [AddCommGroup N] [Module A N] :
    SequentialInverseSystem (ModuleCat A) :=
  Functor.ofOpSequence (X := fun n : ℕ =>
    ModuleCat.of A (N ⧸ I ^ n • (⊤ : Submodule A N)))
    (fun n : ℕ =>
      ModuleCat.ofHom (AdicCompletion.transitionMap I N (Nat.le_add_right n 1)))

noncomputable def qfgseq (I : Ideal A) (N : FGModuleCat A) :
    SequentialInverseSystem (FGModuleCat A) :=
  Functor.ofOpSequence (X := fun n : ℕ =>
    FGModuleCat.of A (N ⧸ I ^ n • (⊤ : Submodule A N)))
    (fun n : ℕ =>
      FGModuleCat.ofHom (AdicCompletion.transitionMap I N (Nat.le_add_right n 1)))

#check qfgseq

def pfg (a : Ideal A) : ObjectProperty (FGModuleCat A) :=
  fun M ↦ Module.IsIdealPowerTorsion a M.obj

instance pfg_serre (a : Ideal A) : (pfg a).IsSerreClass := sorry

noncomputable def qprofg (a I : Ideal A) (N : FGModuleCat A) :=
  (Pro.lim ℕᵒᵖ).obj
    (qfgseq I N ⋙
      (ObjectProperty.SerreClassLocalization.quotientExactFunctor (pfg a)).obj)

#check qprofg

noncomputable def qpro2 (a I : Ideal A) (N : Type u) [AddCommGroup N] [Module A N] :=
  (Pro.lim ℕᵒᵖ).obj
    ((qseq I N ⋙ ModuleCat.uliftFunctor.{u} A) ⋙
      (ObjectProperty.SerreClassLocalization.quotientExactFunctor
        (ModuleCat.isIdealPowerTorsion a)).obj)

#check qseq
#check qpro2

noncomputable def qseq' (I : Ideal A) (N : Type u) [AddCommGroup N] [Module A N] :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  (AdicCompletion.positiveQuotientSystem I N).toSequential

def torsionQ (a : Ideal A) : ModuleCat.{u} A ⥤
    (ModuleCat.isIdealPowerTorsion a).isoModSerre.Localization :=
  (CategoryTheory.ObjectProperty.SerreClassLocalization.quotientExactFunctor
    (ModuleCat.isIdealPowerTorsion a)).obj

noncomputable def testRep (a I : Ideal A) (N : Type u) [AddCommGroup N] [Module A N]
    (X Y : SequentialInverseSystem (ModuleCat.{u} A)) :
    Pro.SequentialHom X Y := sorry

noncomputable def testRepQ (a I : Ideal A) (N : Type u) [AddCommGroup N] [Module A N]
    (X Y : SequentialInverseSystem (ModuleCat.{u} A)) :=
  (testRep a I N X Y).map (torsionQ a)

#check testRepQ

theorem testIso (a I : Ideal A) (N : Type u) [AddCommGroup N] [Module A N]
    (X Y : SequentialInverseSystem (ModuleCat.{u} A))
    (r : Pro.SequentialHom X Y) :
    IsIso ((r.map (torsionQ a)).toHom) := sorry

end Test

namespace AlgebraicGeometry.AffineAlgebraizationSetup
variable {A : Type u} [CommRing A] [IsNoetherianRing A]

noncomputable def coherentModuleOfFinite (N : FGModuleCat A) :
    RingedSpace.Coh (Spec (CommRingCat.of A)).toRingedSpace :=
  ⟨tildeObject N, tilde_isCoherent N⟩

theorem coherentModuleOfFinite_obj (N : FGModuleCat A) :
    (coherentModuleOfFinite N).obj = tildeObject N := sorry

#check coherentModuleOfFinite
#check coherentModuleOfFinite_obj
end AlgebraicGeometry.AffineAlgebraizationSetup

end
