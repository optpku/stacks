/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChernClass.SplittingPrinciple
public import ReasLib.AlgebraicGeometry.ChernClass.Tensor
public import stacks_project.Chap50.Lemma_50_21_1_DeRhamTheory
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped BigOperators

noncomputable section

universe u v

namespace AlgebraicGeometry

open Scheme Scheme.DeRham ChernClass.TotalChernClass

variable (D : ChernTheory.{u}) (c : DeRhamRule D)

/- Remark 50.21.2 (1): a finite family of finite locally free modules on a qcqs scheme
simultaneously acquires invertible-quotient filtrations after a pullback that is injective on
the graded ring underlying an absolute de Rham Chern theory. -/
@[stacks 0FWA] #check
  (AlgebraicGeometry.ChernClass.Theory.existsInjectiveSplittingPullback
    (gradedAlgebra := D.gradedAlgebra) D.toTheory :
    ∀ {ι : Type v} [Finite ι] (X : Scheme.Qcqs.{u}) (E : ι → X.obj.Modules)
      (r : ι → ℕ) [∀ index, Scheme.Modules.IsFiniteLocallyFreeOfRank (r index) (E index)],
    ∃ (P : Scheme.Qcqs.{u}) (p : P ⟶ X),
      Function.Injective (D.A.map p.op) ∧
        ∀ index, Scheme.Modules.HasInvertibleQuotientFiltrationOfLength (r index)
          ((Scheme.Modules.pullback (Qcqs.toScheme.map p)).obj (E index)))

/- Remark 50.21.2 (2): the `i`-th absolute de Rham Chern class of `E ⊗ L` is the
binomial sum of the Chern classes of `E` and powers of the first de Rham Chern class of the
invertible module `L`. -/
@[stacks 0FWA] #check
  (AlgebraicGeometry.ChernClass.TotalChernClass.coeffTensorInvertibleOfRealization
    (gradedAlgebra := D.gradedAlgebra) D.toTheory D.componentEquiv
    (DeRhamRule.ofTotalChernClass D) (DeRhamRule.ofTotalChernClass_surjective D)
    DeRhamRule.app (DeRhamRule.ofTotalChernClass_app D)
    (fun X ↦ (D.chernClass X).deRhamFirstChern) D.firstChernClass_spec c :
    ∀ (X : Scheme.Qcqs.{u})
      (E L : ObjectProperty.FullSubcategory
        (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.obj.Modules))
      (r : ℕ) [Scheme.Modules.IsFiniteLocallyFreeOfRank r E.obj]
      [Scheme.Modules.Invertible L.obj] (i : ℕ),
    ((D.componentEquiv X i).symm
        (c.app X
          (ObjectProperty.GrothendieckGroup.of
            (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.obj.Modules)
            (Scheme.VectorBundleK0.tensorObj X.obj E L)) i) :
      D.A.obj (Opposite.op X)) =
      ∑ j ∈ Finset.range (i + 1),
        (Nat.choose (r + j - i) j : D.A.obj (Opposite.op X)) *
          ((D.componentEquiv X (i - j)).symm
              (c.app X
                (ObjectProperty.GrothendieckGroup.of
                  (SheafOfModules.IsFiniteLocallyFree : ObjectProperty X.obj.Modules) E)
                (i - j)) : D.A.obj (Opposite.op X)) *
          ((D.componentEquiv X 1).symm
              ((D.chernClass X).deRhamFirstChern
                (Scheme.Modules.picardClass L.obj)) : D.A.obj (Opposite.op X)) ^ j)

end AlgebraicGeometry
