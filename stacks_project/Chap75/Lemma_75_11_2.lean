module

public import Mathlib.CategoryTheory.IsomorphismClasses
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import stacks_project.Chap75.Lemma_75_11_2_Coherator
public import stacks_project.Chap75.Lemma_75_11_2_Pushforward

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace
open QCoh.Derived

/-- Lemma 75.11.2. Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic
spaces over `S`. Assume `f` is quasi-compact, quasi-separated, and flat. Writing
`pushforward f` for the right-derived functor of quasi-coherent `f_*`, one has
`coherator Y ∘ Modules.moduleDerivedPushforward f ≅ pushforward f ∘ coherator X`. -/
@[stacks 08GZ]
theorem pushforwardCoherator_isomorphic {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] [Flat f] :
    IsIsomorphic (Modules.moduleDerivedPushforward f ⋙ coherator Y)
      (coherator X ⋙ pushforward f) := sorry

end AlgebraicGeometry.AlgebraicSpace
