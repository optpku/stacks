module

public import stacks_project.Chap82.Lemma_82_32_2_Degree
import StacksCheckRecall

/-!
# Degree formula for zero-cycles on proper algebraic spaces over a field
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Function

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 82.32.2: Let k be a field. Let X be a proper algebraic space over k.
Let α = ∑ n_i [Z_i] be in Z_0(X). Then deg(α) = ∑ n_i deg(Z_i), where
deg(Z_i) is the degree of Z_i ⟶ Spec k, i.e.
deg(Z_i) = dim_k Γ(Z_i, 𝒪_{Z_i}). -/
@[stacks 0ESH]
#check (Hom.zeroCycleDegree_eq_finsum :
  ∀ {k : Type u} [Field k] {X : AlgebraicSpace (Spec (CommRingCat.of k))}
    [Proper (toBase X)] (α : (toBase X).cycleGroup (fun _ ↦ (0 : ℤ)) 0),
    Hom.zeroCycleDegree α =
      ∑ᶠ x : Points X,
        (α : Function.locallyFinsupp (Points X) ℤ) x *
          (Module.finrank k (globalSectionsAlg (PointClosure.space x)) : ℤ))

end AlgebraicGeometry.AlgebraicSpace
