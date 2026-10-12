/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_20_1

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.RigEtale

/-- Lemma 88.20.8: let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S`. If `g ∘ f`
is rig-étale and `g` is an adic monomorphism, then `f` is rig-étale. In Lean
composition this is: if `f ≫ g` is rig-étale and `g` is an adic monomorphism
(`AlgebraicSpace.representableByAlgebraicSpaces g` together with `Mono g`, in
the sense of Definition 87.23.2), then `f` is rig-étale. -/
@[stacks 0GH4]
theorem of_comp_adic_mono {S : Scheme.{u}} {X Y Z : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsFormalAlgebraicSpace Z]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z]
    (f : X ⟶ Y) (g : Y ⟶ Z) [RigEtale (f ≫ g)]
    (hg : AlgebraicSpace.representableByAlgebraicSpaces g) [Mono g] :
    RigEtale f :=
  sorry

end AlgebraicGeometry.FormalAlgebraicSpace.RigEtale
