module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap75.Definition_75_9_1_Square
public import stacks_project.Chap81.Lemma_81_9_2_Relation
public import stacks_project.Chap81.Lemma_81_9_2_Pushout

/-!
# Lemma 81.9.2

An open immersion `ι : V' ⟶ V` and a separated étale morphism `f' : V' ⟶ U` of
algebraic spaces over a scheme `S` admit a pushout in `AlgebraicSpace S`, and the
resulting square is an elementary distinguished square.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare

/-- Lemma 81.9.2 (1). Let `S` be a scheme. Let `V`, `U` be algebraic spaces over `S`.
Let `ι : V' ⟶ V` be an open immersion and let `f' : V' ⟶ U` be a separated étale
morphism of algebraic spaces over `S`. Then the span `(ι, f')` has a pushout
`inl : V ⟶ W`, `inr : U ⟶ W` in `AlgebraicSpace S`. -/
@[stacks 0DVJ]
theorem isPushout_ofOpenSeparatedEtale {S : Scheme.{u}} {U V V' : AlgebraicSpace S}
    (ι : V' ⟶ V) (f' : V' ⟶ U) [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    IsPushout ι f' (inl ι f') (inr ι f') :=
  sorry

/-- Lemma 81.9.2 (2). Let `S` be a scheme. Let `V`, `U` be algebraic spaces over `S`.
Let `ι : V' ⟶ V` be an open immersion and let `f' : V' ⟶ U` be a separated étale
morphism of algebraic spaces over `S`. Then `(U ⊂ W, f : V ⟶ W)` is an elementary
distinguished square. -/
@[stacks 0DVJ]
instance instIsElementaryDistinguishedSquare_ofOpenSeparatedEtale
    {S : Scheme.{u}} {U V V' : AlgebraicSpace S} (ι : V' ⟶ V) (f' : V' ⟶ U)
    [IsOpenImmersion ι] [Etale f'] [Separated f'] :
    IsElementaryDistinguishedSquare (inr ι f') (inl ι f') :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.IsElementaryDistinguishedSquare
