module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap67.Lemma_67_28_8_FinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap108.Lemma_108_5_6_Map
public import stacks_project.Chap108.Lemma_108_10_3_Isom

/-!
# Lemma 108.10.3

With `B`, `Y`, `X` as in the introduction of this section, and assuming in
addition that `X ⟶ B` is proper, the subfunctor of isomorphisms in the
functor of relative morphisms is an open subspace.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Opposite
open AlgebraicGeometry.AlgebraicSpace.Quot (SchemesOver)
open AlgebraicGeometry.AlgebraicSpace.RelativeHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

variable {S : Scheme.{u}} {Y B X : AlgebraicSpace S}

/-- Lemma 108.10.3: with `B`, `Y`, `X` as in the introduction of this section,
in addition assume `X ⟶ B` is proper. Then the subfunctor
`Isom_B(Y, X) ⊂ Mor_B(Y, X)` of isomorphisms is an open subspace. -/
@[stacks 0DPP]
theorem isOpenImmersion_isomι (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [FinitePresentation x] [Proper x] :
    Quot.IsOpenImmersionOnSchemesOver (isomSubfunctor y x).ι :=
  sorry

/-- A `T`-point of `Mor_B(Y, X)` factors through an open of the test scheme if
and only if the restricted relative morphism is an isomorphism. -/
theorem exists_opens_isIso_iff (y : Y ⟶ B) (x : X ⟶ B)
    [Flat y] [Proper y] [FinitePresentation y]
    [FinitePresentation x] [Proper x]
    (σ : SchemesOver B) (b : (mor y x).obj (op σ)) :
    ∃ U : (σ.left.left).Opens,
      ∀ {τ : SchemesOver B} (h : τ ⟶ σ),
        Nonempty (Over.mk h.left.left ⟶ Over.mk U.ι) ↔
          IsIso (restrict y x h b) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
