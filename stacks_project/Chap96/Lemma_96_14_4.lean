module

public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap76.Lemma_76_48_11
public import stacks_project.Chap96.Lemma_96_14_4_Comparison
public import stacks_project.Chap96.Lemma_96_14_4_Restriction
import Mathlib.Tactic.CrossRefAttribute

/-!
# Lemma 96.14.4

For a groupoid in algebraic spaces with flat, locally finitely presented source
and target, atlas restriction of Homs out of a quasi-coherent module on the
quotient stack is injective, and its image is characterised by the 96.10.3.3
comparison diagram on `R_étale`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidsOver
open AlgebraicGeometry.GroupoidAlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
variable (F : QCoh G.quotientStack)
variable (H : RingedSite.ModuleCat.{u} (fppfRingedSite G.quotientStack))

/-- Lemma 96.14.4 (1): let `(U, R, s, t, c)` be a groupoid in algebraic spaces over
`S`. Assume `s, t` are flat and locally of finite presentation. Let `𝒳 = [U / R]`
be the quotient stack, and denote `x` the object of `𝒳` over `U`. Let `ℱ` be a
quasi-coherent `𝒪_𝒳`-module and `ℋ` any object of `Mod(𝒪_𝒳)`. The map
`Hom_{𝒪_𝒳}(ℱ, ℋ) ⟶ Hom_{𝒪_U}(x^* ℱ |_{U_étale}, x^* ℋ |_{U_étale})` given by
`φ ↦ x^* φ |_{U_étale}` is injective. -/
@[stacks 076S]
theorem atlasRestrictHom_injective
    [AlgebraicSpace.Flat G.s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
    [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.t.left] :
    Function.Injective (atlasRestrictHom G F H) :=
  sorry

/-- Lemma 96.14.4 (2): in the situation of Lemma 96.14.4 (1), the image of
`atlasRestrictHom` consists of exactly those
`φ : x^* ℱ |_{U_étale} ⟶ x^* ℋ |_{U_étale}` which give rise to a commutative
diagram of modules on `R_étale` whose horizontal arrows are the comparison maps
of 96.10.3.3 and whose middle identification is `(x ∘ s)^* = (x ∘ t)^*` via
the atlas 2-cell `sourceTarget`. -/
@[stacks 076S]
theorem mem_range_atlasRestrictHom_iff
    [AlgebraicSpace.Flat G.s.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.s.left]
    [AlgebraicSpace.Flat G.t.left]
    [AlgebraicSpace.LocallyOfFinitePresentation G.t.left]
    (φ : atlasRestrictModules G F.obj ⟶ atlasRestrictModules G H) :
    (∃ ψ : F.obj ⟶ H, atlasRestrictHom G F H ψ = φ) ↔
      RespectsComparisons G F H φ :=
  sorry

end AlgebraicGeometry.GroupoidsOver
