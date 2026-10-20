/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Descent.FaithfullyFlat
public import ReasLib.Algebra.Module.DescentDatum.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u

/- Proposition 35.3.9: For a faithfully flat ring map, every module descent
datum is effective, scalar extension is an equivalence onto descent data with
degree-zero invariants as inverse, and the canonical reconstruction map is an
isomorphism. -/
@[stacks 023N] #check
  (Module.DescentDatum.isEffective_of_faithfullyFlat :
    ∀ {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [Module.FaithfullyFlat R A] [AddCommGroup N] [Module R N] [Module A N]
      [IsScalarTower R A N] [SMulCommClass R A N]
      (D : Module.DescentDatum R A N), D.IsEffective)

#check
  (ModuleCat.faithfullyFlatDescentEquivalence :
    ∀ {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A),
      f.FaithfullyFlat →
        (ModuleCat.{u} R ≌
          (ModuleCat.extendRestrictScalarsAdj.{u} f).toComonad.Coalgebra))

#check
  (ModuleCat.faithfullyFlatDescentEquivalence_functor :
    ∀ {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
      (hf : f.FaithfullyFlat),
      (ModuleCat.faithfullyFlatDescentEquivalence f hf).functor =
        CategoryTheory.Comonad.comparison
          (ModuleCat.extendRestrictScalarsAdj.{u} f))

#check
  (ModuleCat.faithfullyFlatDescentEquivalence_inverse :
    ∀ {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
      (hf : f.FaithfullyFlat),
      (ModuleCat.faithfullyFlatDescentEquivalence f hf).inverse =
        ModuleCat.descentPushforward.{u, u, u} f)

#check
  (Module.DescentDatum.reconstruction_isIso_of_faithfullyFlat :
    ∀ {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [Module.FaithfullyFlat R A] [AddCommGroup N] [Module R N] [Module A N]
      [IsScalarTower R A N] [SMulCommClass R A N]
      (D : Module.DescentDatum R A N),
      CategoryTheory.IsIso D.reconstruction)

#check
  (Module.DescentDatum.mem_h0Module_iff :
    ∀ {R A N : Type u} [CommRing R] [CommRing A] [Algebra R A]
      [AddCommGroup N] [Module R N] [Module A N]
      [IsScalarTower R A N] [SMulCommClass R A N]
      (D : Module.DescentDatum R A N) (n : N),
      n ∈ D.h0Module ↔
        (1 : A) ⊗ₜ[R] n = D.equiv (n ⊗ₜ[R] (1 : A)))

#check
  (ModuleCat.descentPushforward_obj :
    ∀ {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
      (D : (ModuleCat.extendRestrictScalarsAdj.{u} f).toComonad.Coalgebra),
      (ModuleCat.descentPushforward.{u, u, u} f).obj D =
        CategoryTheory.Limits.equalizer
          ((ModuleCat.restrictScalars f).map D.a)
          ((ModuleCat.extendRestrictScalarsAdj f).unit.app
            ((ModuleCat.restrictScalars f).obj D.A)))
