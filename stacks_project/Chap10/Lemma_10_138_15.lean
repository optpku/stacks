/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
public import Mathlib.RingTheory.Smooth.NoetherianDescent
import StacksCheckRecall

@[expose] public section

/-! @stack 0CAQ -/

-- Declarations for this item will be appended below by the statement pipeline.

open Algebra CategoryTheory Limits
open scoped TensorProduct

universe u w

section

variable {J : Type u} [Category.{u} J] [IsFiltered J]

/- Domain-style sampling:
* primary domain: smooth commutative algebras and filtered-colimit descent of finitely presented
  algebra data;
* sampled owner declarations:
  `Algebra.Smooth.exists_finiteType`,
  `Algebra.FinitePresentation.of_finiteType`,
  `RingHom.FinitePresentation.comp`,
  `finitelyPresented_algebra_is_baseChange_of_stage`;
* best owner abstraction: `Smooth`, with finite-presentation descent treated as derived bridge API;
* layer triage:
  - `source-facing`: the filtered-colimit descent theorem for a smooth algebra over `c.pt`;
  - `core/canonical`: the owner predicate `Smooth`;
  - `bridge/view`: factoring the finite-type model through a stage and recovering `B` by tensor
    base change;
* primitive data: the filtered diagram `F`, its colimit cocone `c`, and the smooth `c.pt`-algebra
  `B`;
* derived API: the finite-type model from `Algebra.Smooth.exists_finiteType`, the finite
  presentation of that model, and the stagewise base-change recovery.
-/

-- Proof sketch: first apply `Algebra.Smooth.exists_finiteType` to descend the smooth algebra over
-- the colimit ring to a smooth algebra over a finite-type intermediate ring. Since a finite-type
-- algebra is finitely presented, Lemma `10.127.3` factors the structure map of that intermediate
-- ring through some stage of the filtered diagram. This yields a stage algebra whose primary
-- owner-level property is smoothness; base changing that smooth model along the stage map then
-- recovers `B` as companion bridge data.
/-- Lemma 10.138.15: if `c` is a filtered colimit cocone of commutative rings and `B` is smooth
over the colimit ring `c.pt`, then `B` is obtained by base change from a smooth algebra over some
stage of the diagram. The descended stage algebra naturally lives in the universe of the diagram
stages, and the tensor-product equivalence back to `B` is companion bridge data. -/
@[stacks 0CAQ]
theorem smooth_is_baseChange_of_stage_of_isColimit
    (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_hc : IsColimit c)
    (B : Type w) [CommRing B] [Algebra c.pt B] [Smooth c.pt B] :
    ∃ (j : J) (B_j : Type u) (_ : CommRing B_j) (_ : Algebra (F.obj j) B_j),
      letI : Algebra (F.obj j) c.pt := (c.ι.app j).hom.toAlgebra
      Smooth (F.obj j) B_j ∧ Nonempty (B ≃ₐ[c.pt] c.pt ⊗[F.obj j] B_j) := sorry

end
