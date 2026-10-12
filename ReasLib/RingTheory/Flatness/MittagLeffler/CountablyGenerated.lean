/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimit.CountablyGenerated
public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation
public import ReasLib.CategoryTheory.Functor.TailFactorization.Presentation
public import ReasLib.RingTheory.Flatness.MittagLeffler.TailFactorization
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Countably Generated Mittag-Leffler Modules

This file records the finite-stage approximation API for countably generated Mittag-Leffler
modules, both for a concrete directed presentation and intrinsically for the presented module.
-/

open CategoryTheory CategoryTheory.Limits

universe u v w x

namespace Module.IsMittagLefflerDirectedSystem

variable {R : Type u} [Ring R]
variable {I : Type w} [Preorder I] [Nonempty I] [IsDirectedOrder I]
variable {F : I ⥤ ModuleCat.{v} R} [HasColimit F]

/-- For a Mittag-Leffler presentation with countably generated colimit, every structure map is
fixed by an endomorphism of the colimit that factors through one stage. -/
@[stacks 05D2 "stage"]
theorem exists_factorization_ι (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R
      (colimit F : ModuleCat.{v} R)) (i : I) :
    ∃ (j : I) (g : colimit F ⟶ F.obj j),
      colimit.ι F i ≫ g ≫ colimit.ι F j = colimit.ι F i := sorry

/-- Linear-map form of
`Module.IsMittagLefflerDirectedSystem.exists_factorization_ι`. -/
theorem exists_linearMap_factorization_ι (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R
      (colimit F : ModuleCat.{v} R)) (i : I) :
    ∃ j, ∃ g : (colimit F : ModuleCat.{v} R) →ₗ[R] F.obj j,
      (((colimit.ι F j).hom :
          F.obj j →ₗ[R] (colimit F : ModuleCat.{v} R)) ∘ₗ g) ∘ₗ
        ((colimit.ι F i).hom :
          F.obj i →ₗ[R] (colimit F : ModuleCat.{v} R)) =
      ((colimit.ι F i).hom :
        F.obj i →ₗ[R] (colimit F : ModuleCat.{v} R)) := sorry

/-- A map from a finite module into a countably generated Mittag-Leffler colimit is fixed by an
endomorphism of the colimit that factors through one stage. -/
@[stacks 05D2 "presentation"]
theorem exists_factorization
    {P : Type x} [AddCommGroup P] [Module R P] [Module.Finite R P]
    (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R
      (colimit F : ModuleCat.{v} R))
    (f : P →ₗ[R] (colimit F : ModuleCat.{v} R)) :
    ∃ i, ∃ g : (colimit F : ModuleCat.{v} R) →ₗ[R] F.obj i,
      (((colimit.ι F i).hom :
        F.obj i →ₗ[R] (colimit F : ModuleCat.{v} R)) ∘ₗ g) ∘ₗ f = f := sorry

/-- A Mittag-Leffler directed system with countably generated colimit has a countable directed
subsystem whose restricted cocone still presents the original colimit. -/
@[stacks 059W "presentation"]
theorem exists_countable_subpresentation (hF : IsMittagLefflerDirectedSystem F)
    (hcg : Module.CountablyGenerated R
      (colimit F : ModuleCat.{v} R)) :
    ∃ (S : Set I) (_ : Countable S) (_ : Nonempty S) (_ : IsDirectedOrder S),
      (ColimitPresentation.colimit F).IsColimitRestriction S := sorry

end Module.IsMittagLefflerDirectedSystem

namespace Module.MittagLeffler

variable {R : Type u} [Ring R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {P : Type w} [AddCommGroup P] [Module R P] [Module.Finite R P]

/-- Lemma 10.92.2 (05D2): a map from a finite module to a countably generated Mittag-Leffler
module is fixed by an endomorphism factoring through a finitely presented module. -/
@[stacks 05D2]
theorem exists_finitePresentation_factorization (hML : MittagLeffler R M)
    (hcg : Module.CountablyGenerated R M) (f : P →ₗ[R] M) :
    ∃ (Q : ModuleCat.{v} R) (_ : Module.FinitePresentation R Q)
      (g : M →ₗ[R] Q) (h : Q →ₗ[R] M), (h ∘ₗ g) ∘ₗ f = f := sorry

/-- Lemma 10.92.1, tag `059W`: every finitely presented directed colimit presentation of a
countably generated Mittag-Leffler module contains a countable directed subsystem with the same
colimit. -/
@[stacks 059W]
theorem exists_countable_subpresentation (hML : MittagLeffler R M)
    (hcg : Module.CountablyGenerated R M) {I : Type w} [Preorder I] [Nonempty I]
    [IsDirectedOrder I]
    (P : ColimitPresentation I (ModuleCat.of.{v} R M))
    (hfp : ∀ i, Module.FinitePresentation R (P.diag.obj i)) :
    ∃ (S : Set I) (_ : Countable S) (_ : Nonempty S) (_ : IsDirectedOrder S),
      P.IsColimitRestriction S := sorry

end Module.MittagLeffler
