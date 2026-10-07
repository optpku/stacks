module

public import stacks_project.Chap70.Lemma_70_9_6_Finite
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.QcAlgebraUnder

universe u

/- Lemma 70.9.6: let `S` be a scheme. Let `X` be a quasi-compact and quasi-separated algebraic
space over `S`. Let `A` be a finite quasi-coherent `𝒪_X`-algebra. Then `A` is a directed colimit
of finite and finitely presented quasi-coherent `𝒪_X`-algebras with surjective transition maps. -/
@[stacks 086Z] #check
  (exists_finite_finitelyPresentable_colimitPresentation_locallySurjective :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} [IsQuasiCompact X]
      [IsAbsolutelyQuasiSeparated X] (A : X.QcAlgebraUnder) [IsFinite A],
      ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I),
        ∃ pres : ColimitPresentation I A.obj,
          (∀ i : I, finiteProperty X (pres.diag.obj i)) ∧
            (∀ i : I, finitelyPresentableProperty X (pres.diag.obj i)) ∧
              ∀ {i i' : I} (f : i ⟶ i'),
                Sheaf.IsLocallySurjective (pres.diag.map f).right)
