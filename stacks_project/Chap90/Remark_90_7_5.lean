module

public import stacks_project.Chap90.Remark_90_7_5_AlongOver

/-!
# Completion along a family of filtrations inducing the maximal-adic topology

Given a category cofibered in groupoids over `C_Λ` and a family of ideal
filtrations inducing the maximal-adic topology, one obtains a cofibered
category `hat F_I` over `hat C_Λ` whose fibres recover the `Along` fibres
and which is equivalent to ordinary completion by Lemma 90.7.4.
-/

@[expose] public section

open CategoryTheory FormalObject CompleteLocalAlgCat

universe u v

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{v} F]

/-- Remark 90.7.5 (1): given `p : F ⥤ ArtinianLocalAlgCat Λ k` cofibered in
groupoids and a family `I` assigning to each `R` in `CompleteLocalAlgCat Λ k`
an ideal filtration inducing the `m_R`-adic topology, mimicking
`Functor.completion` yields a functor
`Functor.completionAlong I p : FormalObject.AlongOver p I ⥤ CompleteLocalAlgCat Λ k`
making `hat F_I` into a category cofibered in groupoids over `hat C_Λ`. -/
@[stacks 06H7]
instance Functor.completionAlong_op_isFiberedInGroupoids
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    Functor.IsFibered.InGroupoids (Functor.completionAlong I p).op := sorry

/-- Remark 90.7.5 (2): the fibre `hat F_I(R)` is isomorphic to the fibre category
`hat F_{I R}(R)` of inverse systems along `I R`, via the equivalence
`FormalObject.AlongOver.ofAlong p I R`. -/
@[stacks 06H7]
instance FormalObject.AlongOver.ofAlong_isEquivalence
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op]
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (R : CompleteLocalAlgCat Λ k) :
    (FormalObject.AlongOver.ofAlong p I R).IsEquivalence := sorry

/-- Remark 90.7.5 (3): the cofibered categories `hat F_I` and `hat F` are
equivalent over `hat C_Λ` by using over each `R` the equivalence of
Lemma 90.7.4, packaged as `FormalObject.AlongOver.toCompletionBased`. -/
@[stacks 06H7]
instance FormalObject.AlongOver.toCompletion_isEquivalence
    (I : ∀ R : CompleteLocalAlgCat Λ k, AdicIdealFiltration R)
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsFibered.InGroupoids p.op] :
    BasedFunctor.IsEquivalence (FormalObject.AlongOver.toCompletionBased I p) := sorry

end
