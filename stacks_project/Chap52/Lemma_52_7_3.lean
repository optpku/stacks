/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Lemma_52_6_20
public import stacks_project.Chap52.Lemma_52_7_2
public import ReasLib.CategoryTheory.DerivedCategory.HomotopyLimit.Cohomology
public import ReasLib.CategoryTheory.DerivedCategory.Limit.MilnorTriangle
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Ideal.PowerQuotient.Module
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Perfect.FlatPullbackSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.RingedSpace
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Spec
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open RingedSite.Hom.ModuleDerived
open SheafOfModules.RingedSite.IdealSheaf
open SheafOfModules.RingedSite.IdealSheaf.PowerQuotientModule

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived
namespace DerivedCompletion

/-- The inverse system whose stage `n` is the degree-`p` cohomology of
`F / I ^ (n + 1) F` over `A`, represented by the positive shifted quotient tower. -/
noncomputable abbrev quotientCohomologySystem
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (F : X.Modules) (p : ℤ) :
    SequentialInverseSystem (ModuleCat.{u} A) :=
  SequentialInverseSystem.shift
      (PowerQuotientModule.system.{u, u, u}
        (((idealSheafDataOfIdealOnSpec I).comap f).toSubobject)
        ((Scheme.Modules.toRingedSpace X).obj F)) 1 ⋙
    Scheme.Modules.fromRingedSpace X ⋙
    ModuleCech.moduleToDerived X ⋙
    Scheme.FlatPullbackSections.baseSections f ⋙
    DerivedCategory.homologyFunctor (ModuleCat.{u} A) p

/-- Stage `n` of `quotientCohomologySystem f I F p` is the cohomology of the
positive quotient stage at exponent `n + 1`. -/
theorem quotientCohomologySystem_obj
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (F : X.Modules) (p : ℤ) (n : ℕ) :
    (quotientCohomologySystem f I F p).obj (op n) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
        ((Scheme.FlatPullbackSections.baseSections f).obj
          ((ModuleCech.moduleToDerived X).obj
            ((Scheme.Modules.fromRingedSpace X).obj
              ((PowerQuotientModule.system.{u, u, u}
                (((idealSheafDataOfIdealOnSpec I).comap f).toSubobject)
                ((Scheme.Modules.toRingedSpace X).obj F)).obj (op (n + 1)))))) := sorry

/-- The successor map of `quotientCohomologySystem f I F p` is induced by the
canonical transition between the corresponding quotient stages. -/
theorem quotientCohomologySystem_stepMap
    {A : Type u} [CommRing A] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (F : X.Modules) (p : ℤ) (n : ℕ) :
    (quotientCohomologySystem f I F p).stepMap n =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).map
        ((Scheme.FlatPullbackSections.baseSections f).map
          ((ModuleCech.moduleToDerived X).map
            (PowerQuotientModule.step
              (((idealSheafDataOfIdealOnSpec I).comap f).toSubobject)
              ((Scheme.Modules.toRingedSpace X).obj F) (1 + n)))) := sorry

/-- Lemma 52.7.3 (1): for a Noetherian ring `A`, a Noetherian scheme `X` over
`Spec A`, and a coherent module `F` with finite cohomology in every degree,
the `I`-adic completion of cohomology fits into the Milnor short exact sequence
with the positive quotient cohomology tower. -/
@[stacks 0A0M]
theorem cohomologyShortExact
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (F : X.Modules) [F.IsCoherent]
    (hfinite : ∀ q : ℤ,
      Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
          ((Scheme.FlatPullbackSections.baseSections f).obj
            ((ModuleCech.moduleToDerived X).obj F))))
    (p : ℤ) :
    ∃ (ι :
        (quotientCohomologySystem f I F (p - 1)).firstDerivedLimit ⟶
          ModuleCat.of A
            (AdicCompletion I
              (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
                ((Scheme.FlatPullbackSections.baseSections f).obj
                  ((ModuleCech.moduleToDerived X).obj F)) : Type u))))
      (π :
        ModuleCat.of A
            (AdicCompletion I
              (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
                ((Scheme.FlatPullbackSections.baseSections f).obj
                  ((ModuleCech.moduleToDerived X).obj F)) : Type u))) ⟶
          limit (quotientCohomologySystem f I F p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact := sorry

/-- Lemma 52.7.3 (2): under the same Noetherian, coherence, and finite-cohomology
hypotheses, if `f` is proper then the first derived limit of the positive
quotient cohomology tower vanishes in every degree. -/
@[stacks 0A0M]
theorem firstDerivedLimitIsZeroOfProper
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (I : Ideal A) (F : X.Modules) [F.IsCoherent]
    (hfinite : ∀ q : ℤ,
      Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
          ((Scheme.FlatPullbackSections.baseSections f).obj
            ((ModuleCech.moduleToDerived X).obj F))))
    (p : ℤ) :
    IsZero (quotientCohomologySystem f I F (p - 1)).firstDerivedLimit := sorry

end DerivedCompletion
end AlgebraicGeometry.Scheme.ModuleDerived

end
