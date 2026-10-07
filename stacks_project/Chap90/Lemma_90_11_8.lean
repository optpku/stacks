module

public import stacks_project.Chap90.Lemma_90_11_8_Eval
public import stacks_project.Chap90.Lemma_90_11_8_FGOver

/-!
# Lemma 90.11.8

A functor on a strictly full subcategory of `S`-Alg/`R` containing every
`R[M]` acquires a natural `R`-module structure on `F(R[M])` when `F(R)` is a
singleton and fibre products of `R[M]` are sent bijectively to products of
values.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits
open TrivSqZeroExt

universe u

namespace CategoryTheory.Functor

variable {S R : Type u} [CommRing S] [CommRing R] [Algebra S R]

/-- Lemma 90.11.8: Let `R` be an `S`-algebra, and let `C` be a strictly full
subcategory of `S`-Alg/`R` containing `R[M]` for all finitely generated
`R`-modules `M`. Let `F : C ⥤ Type` be a functor. Suppose that `F(R)` is a
one-element set and that for any finitely generated `R`-modules `M, N` the
induced map `F(R[M] ×_R R[N]) ⟶ F(R[M]) × F(R[N])` is a bijection. Then
`F(R[M])` has a natural `R`-module structure for any finitely generated
`R`-module `M`. -/
@[stacks 06IA]
theorem module_fgEval (P : ObjectProperty (Over (CommAlgCat.of S R)))
    [P.IsClosedUnderIsomorphisms] [P.ContainsFGTrivSqZeroExt]
    (F : P.FullSubcategory ⥤ Type u) [Unique (F.obj (overSelfObj P))]
    [F.BijectiveOnFGSquareZeroProds] (M : FGModuleCat.{u} R) :
    (linearLift (fgEval P F)).obj M =
      ModuleCat.of R ((fgEval P F).obj M) := sorry

end CategoryTheory.Functor
