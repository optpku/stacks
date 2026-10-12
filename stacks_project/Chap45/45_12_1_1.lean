/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap45.«45_12_1_1_ChernClasses»
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.ChernClass

universe u v w x

/- 45.12.1.1: if `E` is finite locally free of constant rank `r`,
`p : P ⟶ X` is its projective bundle, and `A` is the graded cohomology algebra, then
the alternating sum of `c₁(𝒪_P(1)) ^ i` cup `p^* cⱼ_{r-i}(E)` is zero. -/
@[stacks 0FI6] #check
  (AlgebraicGeometry.ChernClass.ProjectiveBundleContext.chernClass_relation :
    ∀ {C : Type u} [Category.{v} C] (toScheme : C ⥤ Scheme.{w})
      (A : Cᵒᵖ ⥤ RingCat.{x}) (X P : C) (E : (toScheme.obj X).Modules) (r : ℕ)
      [Scheme.Modules.IsFiniteLocallyFreeOfRank r E]
      (p : P ⟶ X)
      (hP : Scheme.ProjectiveBundle.Representation (toScheme.map p) E)
      (S : AlgebraicGeometry.ChernClass.ProjectiveBundleContext toScheme A X P E r p hP),
      ∑ i : Fin (r + 1),
        (-1 : A.obj (Opposite.op P)) ^ i.1 *
          S.tautologicalFirstChernClass ^ i.1 *
            A.map p.op
              (AlgebraicGeometry.ChernClass.ProjectiveBundleContext.chernClass
                toScheme A X P E r p hP S (Fin.rev i)) = 0)
