module

public import ReasLib.AlgebraicTopology.CosimplicialObject.Abelian
import StacksCheckRecall

/-!
@stack 018Z

# Source-facing recall for Lemma 14.22.1

Abelian structures and monomorphism/epimorphism detection are canonical functor-category API.
ReasLib supplies the matching pointwise exactness criterion for short complexes.
-/

@[expose] public section

universe v u

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A]

/- Lemma 14.22.1 (1): simplicial and cosimplicial objects in `A` form abelian categories. -/
@[stacks 018Z "Lemma 14.22.1 (1), simplicial objects"]
#check (inferInstance : Abelian (SimplicialObject A))

@[stacks 018Z "Lemma 14.22.1 (1), cosimplicial objects"]
#check (inferInstance : Abelian (CosimplicialObject A))

variable {X Y : SimplicialObject A} (f : X ⟶ Y)
variable {X' Y' : CosimplicialObject A} (f' : X' ⟶ Y')

/- Lemma 14.22.1 (2): monomorphisms of (co)simplicial objects are detected degreewise. -/
@[stacks 018Z "Lemma 14.22.1 (2), simplicial monomorphisms"]
#check
  (NatTrans.mono_iff_mono_app
      (K := SimplexCategoryᵒᵖ) (C := A) (f := f) :
    Mono f ↔ ∀ n : SimplexCategoryᵒᵖ, Mono (f.app n))

@[stacks 018Z "Lemma 14.22.1 (2), cosimplicial monomorphisms"]
#check
  (NatTrans.mono_iff_mono_app
      (K := SimplexCategory) (C := A) (f := f') :
    Mono f' ↔ ∀ n : SimplexCategory, Mono (f'.app n))

/- Lemma 14.22.1 (3): epimorphisms of (co)simplicial objects are detected degreewise. -/
@[stacks 018Z "Lemma 14.22.1 (3), simplicial epimorphisms"]
#check
  (NatTrans.epi_iff_epi_app
      (K := SimplexCategoryᵒᵖ) (C := A) (f := f) :
    Epi f ↔ ∀ n : SimplexCategoryᵒᵖ, Epi (f.app n))

@[stacks 018Z "Lemma 14.22.1 (3), cosimplicial epimorphisms"]
#check
  (NatTrans.epi_iff_epi_app
      (K := SimplexCategory) (C := A) (f := f') :
    Epi f' ↔ ∀ n : SimplexCategory, Epi (f'.app n))

variable (S : ShortComplex (SimplicialObject A))
variable (S' : ShortComplex (CosimplicialObject A))

/- Lemma 14.22.1 (4): exactness of sequences of (co)simplicial objects is detected degreewise. -/
@[stacks 018Z "Lemma 14.22.1 (4), simplicial exactness"]
#check
  (ShortComplex.exact_iff_forall_app
      (K := SimplexCategoryᵒᵖ) (A := A) S :
    S.Exact ↔ ∀ n : SimplexCategoryᵒᵖ,
      (S.map ((CategoryTheory.evaluation SimplexCategoryᵒᵖ A).obj n)).Exact)

@[stacks 018Z "Lemma 14.22.1 (4), cosimplicial exactness"]
#check
  (CosimplicialObject.exact_iff_forall_app S' :
    S'.Exact ↔ ∀ n : SimplexCategory,
      (S'.map (CosimplicialObject.evaluation A n)).Exact)

end CategoryTheory
