module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Colimit.Evaluation
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
public import stacks_project.Chap92.«92_4_0_1_Polynomial»
import Mathlib.Tactic.CrossRefAttribute

/-!
# Finite cohomology of derived lower shriek

Lemma 92.5.3 records that if `A` is Noetherian, `A → B` is of finite type, and an
`underline{B}`-module on `C_{B/A}` takes finite values on finite-type polynomial objects,
then every cohomology module of `Lπ!(F)` is a finite `B`-module.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open Opposite
open Algebra
open Algebra.PolynomialSite
open CommAlgCat.Over.Polynomial (ofMvPolynomial)
open scoped CategoryTheory

universe u q q'

namespace Algebra.PolynomialSite

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [Algebra.FiniteType A B]
variable [HasColimitsOfShape (PolynomialSite A B)ᵒᵖ (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q'} (ModuleCat.{u} B)]
variable [HasDerivedCategory.{q} ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)]
variable [Functor.HasLeftDerivedFunctor
  (categoryOverPointColimitToDerived (PolynomialSite A B) (ModuleCat.{u} B))
  (HomotopyCategory.quasiIso ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (ComplexShape.up ℤ))]

/-- Lemma 92.5.3. Let `A` be a Noetherian ring, let `A → B` be a finite type ring map, and
let `π` and `underline{B}` be as in 92.4.0.1. If `F` is an `underline{B}`-module on
`C_{B/A}` such that `F.obj Y` is a finite `B`-module whenever the source of `Y` is a
finite-type polynomial `A`-algebra, then every cohomology module of `Lπ!(F)` is a finite
`B`-module. -/
@[stacks 08PY]
theorem lowerShriek_homology_finite
    (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (h_eval : ∀ (Y : (PolynomialSite A B)ᵒᵖ),
      Algebra.FiniteType A Y.unop.unop.obj.left → Module.Finite B (F.obj Y))
    (i : ℤ) :
    Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        (((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
            (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj F)) :=
  sorry

/-- If `F` takes finite `B`-module values on every augmentation
`α : MvPolynomial ι A →ₐ[A] B` with `ι` finite, then every cohomology module of `Lπ!(F)`
is a finite `B`-module. -/
theorem lowerShriek_homology_finite_of_mvPolynomial
    (F : (PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
    (h_eval : ∀ (ι : Type u) [Finite ι] (α : MvPolynomial ι A →ₐ[A] B),
      Module.Finite B (F.obj (op (op (ofMvPolynomial A B ι α)))))
    (i : ℤ) :
    Module.Finite B
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).obj
        (((DerivedCategory.singleFunctor ((PolynomialSite A B)ᵒᵖ ⥤ ModuleCat.{u} B)
            (0 : ℤ)) ⋙
          Lπ![(PolynomialSite A B), (ModuleCat.{u} B)]).obj F)) :=
  sorry

end Algebra.PolynomialSite
