module

public import Mathlib.CategoryTheory.Equivalence
public import stacks_project.Chap90.Definition_90_7_3
public import stacks_project.Chap90.Lemma_90_7_4_Along
public import stacks_project.Chap90.Lemma_90_7_4_Filtration

/-!
# Independence of the completion fibre from the ideal filtration

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids, the fibre of
inverse systems over truncations `R ⧸ I n` is equivalent to the ordinary
completion fibre `Fiber (Functor.completion p) R`.
-/

@[expose] public section

open CategoryTheory CompleteLocalAlgCat

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]
variable {p : F ⥤ ArtinianLocalAlgCat Λ k} [Functor.IsFibered.InGroupoids p.op]
variable {R : CompleteLocalAlgCat Λ k} (I : AdicIdealFiltration R)

/-- Lemma 90.7.4: if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and
`I` is a decreasing ideal filtration of `R` inducing the maximal-adic topology,
then the fibre category of inverse systems over `R ⧸ I n` is equivalent to the
ordinary completion fibre `Fiber (Functor.completion p) R`. -/
@[stacks 06H6]
instance FormalObject.Along.toFiber_isEquivalence :
    (FormalObject.Along.toFiber p R I).IsEquivalence := sorry
