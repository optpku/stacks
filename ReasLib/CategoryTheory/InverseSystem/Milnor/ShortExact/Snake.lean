module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import ReasLib.CategoryTheory.InverseSystem.Milnor.ShortExact.Universal
public import ReasLib.CategoryTheory.InverseSystem.ShortExact
import Mathlib.Tactic.CrossRefAttribute

/-!
# The Milnor Snake Sequence

This leaf supplies exactness of the product rows and packages the row diagram into the snake
lemma. Its connecting morphism and exact sequence are the canonical six-term Milnor API for a
short exact row of sequential inverse systems of abelian groups.
@stack 0H31
-/

@[expose] public section

open CategoryTheory.Limits Opposite

noncomputable section

universe v

namespace CategoryTheory.ShortComplex.ShortExact

open SequentialInverseSystem.Milnor SequentialInverseSystem.Milnor.ProductCone

/-- Products preserve exactness of a short exact row of sequential abelian groups. -/
@[stacks 0H31 "exactness of the Milnor product row"]
theorem productRow_exact
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) (hS : S.ShortExact) :
    (productRow S).Exact := sorry

/-- The right map of the product row associated to a short exact sequential row is epic. -/
@[stacks 0H31 "epimorphic right map of the Milnor product row"]
theorem productRow_epi_g
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) (hS : S.ShortExact) :
    Epi (productRow S).g := sorry

/-- The left map of the product row associated to a short exact sequential row is monic. -/
@[stacks 0H31 "monomorphic left map of the Milnor product row"]
theorem productRow_mono_f
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) (hS : S.ShortExact) :
    Mono (productRow S).f := sorry

/-- The canonical snake-lemma input for the Milnor product diagram of a short exact sequential
row. Its non-Prop fields are the explicit limit, product, difference, and cokernel maps; the
kernel, cokernel, and exactness laws are deferred proof obligations. -/
@[stacks 0H31 "Milnor snake-lemma input"]
noncomputable def limitR1SnakeInput
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) (hS : S.ShortExact) :
    SnakeInput AddCommGrpCat.{v} where
  L₀ := S.map (lim : SequentialInverseSystem AddCommGrpCat.{v} ⥤ AddCommGrpCat.{v})
  L₁ := productRow S
  L₂ := productRow S
  L₃ := r1Row S
  v₀₁ := limitToProductHom S
  v₁₂ := milnorDifferenceHom S
  v₂₃ := productToR1Hom S
  w₀₂ := limitToProductHom_comp_milnorDifferenceHom S
  w₁₃ := milnorDifferenceHom_comp_productToR1Hom S
  h₀ := limitToProductHom_isLimit S
  h₃ := productToR1Hom_isColimit S
  L₁_exact := productRow_exact S hS
  epi_L₁_g := productRow_epi_g S hS
  L₂_exact := productRow_exact S hS
  mono_L₂_f := productRow_mono_f S hS

/-- The canonical connecting morphism
`lim S.X₃ ⟶ SequentialInverseSystem.Milnor.ProductCone.canonicalR1 S.X₁` of the Milnor
six-term sequence. -/
@[stacks 0H31 "Milnor connecting morphism"]
noncomputable def limitR1Connecting
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) (hS : S.ShortExact) :
    limit S.X₃ ⟶ canonicalR1 S.X₁ :=
  (limitR1SnakeInput S hS).δ

/-- Lemma 15.87.2 [0H31]: a short exact sequence of sequential inverse systems of abelian
groups gives the central exact five-term portion of the Milnor six-term sequence. -/
@[stacks 0H31]
theorem limitR1_exact
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) (hS : S.ShortExact) :
    (ComposableArrows.mk₅
      (lim.map S.f)
      (lim.map S.g)
      (limitR1Connecting S hS)
      (canonicalR1.map S.f)
      (canonicalR1.map S.g)).Exact := sorry

/-- The first map in the Milnor six-term sequence of a short exact sequential row is monic. -/
@[stacks 0H31 "monomorphic first map of the Milnor sequence"]
theorem limit_mono_map_f
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) (hS : S.ShortExact) :
    Mono (lim.map S.f) := sorry

/-- The last map in the Milnor six-term sequence of a short exact sequential row is epic. -/
@[stacks 0H31 "epimorphic last map of the Milnor sequence"]
theorem r1_epi_map_g
    (S : ShortComplex (SequentialInverseSystem AddCommGrpCat.{v})) (hS : S.ShortExact) :
    Epi (canonicalR1.map S.g) := sorry

end CategoryTheory.ShortComplex.ShortExact
