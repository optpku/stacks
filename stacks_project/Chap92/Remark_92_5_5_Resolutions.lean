/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap92.Remark_92_5_5_Resolutions_Resolution
public import stacks_project.Chap92.Lemma_92_4_1
public import stacks_project.Chap92.Lemma_92_4_3
public import stacks_project.Chap92.Lemma_92_7_1_Omega
public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import ReasLib.AlgebraicTopology.SimplicialObject.HomotopyEquiv
import StacksCheckRecall
import Mathlib.Tactic.CrossRefAttribute

/-!
# Polynomial simplicial resolutions of an algebra

Remark 92.5.5 packages a resolution of `B` over `A` as a polynomial simplicial
augmentation whose underlying map is a trivial Kan fibration, records the equivalent
characterizations, and notes that any such resolution computes `Lπ!` and `L_{B/A}`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.SimplicialObject
open Algebra
open Algebra.PolynomialSite
open Algebra.CotangentComplex
open CommAlgCat.Over.Polynomial.Site
open SSet.modelCategoryQuillen
open AlgebraicTopology
open HomologicalComplex
open scoped CategoryTheory

universe u q

/- Remark 92.5.5 (Resolutions) (1): a resolution of `B` over `A` is an augmented
simplicial `A`-algebra `ε : P ⟶ B` with each `P.obj n` a polynomial `A`-algebra and
with `ε` a trivial Kan fibration of simplicial sets. -/
@[stacks 08QI]
#check IsResolution

namespace Algebra.PolynomialSite

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))

/-- Remark 92.5.5 (Resolutions) (2): if each `P.obj n` is a polynomial `A`-algebra
surjecting onto `B`, then `ε` being a resolution, a quasi-isomorphism on associated
complexes, and a homotopy equivalence of simplicial sets are equivalent, by Simplicial
Lemmas 14.30.8, 14.31.9, and 14.31.8. -/
@[stacks 08QI]
theorem isResolution_tfae (hP : ∀ n, IsPolynomial A (P.obj n))
    (h_surj : ∀ n, Function.Surjective ((forget (CommAlgCat.{u} A)).map (ε.app n))) :
    List.TFAE
      [IsResolution ε,
        QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
          (underlyingAddCommGrpMap ε)),
        IsHomotopyEquivalence (underlyingSSetMap ε)] :=
  sorry

/-- Under the polynomial and degreewise-surjective hypotheses, being a resolution is
equivalent to the associated-complex map being a quasi-isomorphism. -/
theorem isResolution_iff_quasiIso (hP : ∀ n, IsPolynomial A (P.obj n))
    (h_surj : ∀ n, Function.Surjective ((forget (CommAlgCat.{u} A)).map (ε.app n))) :
    IsResolution ε ↔
      QuasiIso ((alternatingFaceMapComplex AddCommGrpCat.{u}).map
        (underlyingAddCommGrpMap ε)) :=
  sorry

/-- Under the polynomial and degreewise-surjective hypotheses, being a resolution is
equivalent to the underlying simplicial-set map being a homotopy equivalence. -/
theorem isResolution_iff_homotopyEquivalence (hP : ∀ n, IsPolynomial A (P.obj n))
    (h_surj : ∀ n, Function.Surjective ((forget (CommAlgCat.{u} A)).map (ε.app n))) :
    IsResolution ε ↔ IsHomotopyEquivalence (underlyingSSetMap ε) :=
  sorry

end Algebra.PolynomialSite

/- Remark 92.5.5 (Resolutions) (3): a resolution `P` of `B` over `A` yields a
cosimplicial object of `PolynomialSite A B` as in Cohomology on Sites, Lemma 21.39.7,
and `Lπ! F` is isomorphic to the evaluation of `F` on `(P, ε)` by Lemma 92.4.1. -/
@[stacks 08QI]
#check lowerShriek_eval_abelian
@[stacks 08QI]
#check lowerShriek_eval_module

namespace Algebra.PolynomialSite

/-- Remark 92.5.5 (Resolutions) (4): resolutions exist for every ring map `A → B`.
The formal part of the proof of Proposition 92.5.2 produces a resolution without
appealing to the simplicial computations in Simplicial, Section 14.34. -/
@[stacks 08QI]
theorem exists_resolution (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] :
    ∃ (P : SimplicialObject (CommAlgCat.{u} A))
      (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B)),
      IsResolution ε :=
  sorry

end Algebra.PolynomialSite

/- Remark 92.5.5 (Resolutions) (5): the standard resolution of `B` over `A` is a
resolution, as in the first proof of Lemma 92.4.2, so the terminology does not
conflict. -/
@[stacks 08QI]
#check instIsResolution_standardHom

namespace Algebra.CotangentComplex

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable {P : SimplicialObject (CommAlgCat.{u} A)}
variable (ε : P ⟶ (const (CommAlgCat.{u} A)).obj (CommAlgCat.of A B))
variable [HasDerivedCategory.{q} (ModuleCat.{u} B)]

/-- Remark 92.5.5 (Resolutions) (6): for any resolution `ε`, there is a canonical
isomorphism in `D(B)` between `Algebra.cotangentComplex A B` and the evaluation of
`omegaSheaf A B` on `IsResolution.asCosimplicial ε`, by Lemma 92.4.3. The freedom to
choose an arbitrary resolution can be quite useful. -/
@[stacks 08QI]
theorem cotangentComplex_iso_eval [IsResolution ε] :
    IsIsomorphic
      (DerivedCategory.Q.obj (Algebra.cotangentComplex A B))
      ((CosimplicialObject.Evaluation.toDerived (ModuleCat.{u} B)
          (IsResolution.asCosimplicial ε)).obj (omegaSheaf A B)) :=
  sorry

end Algebra.CotangentComplex
