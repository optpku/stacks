/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import stacks_project.Chap76.Lemma_76_7_8_Transitivity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FormallySmooth

/-!
# Short exactness of the transitivity sequence under formal smoothness

If `f : X ⟶ Y` is a formally smooth morphism of algebraic spaces, the canonical
transitivity sequence of Lemma 76.7.8 is short exact.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open Hom.Differentials.Transitivity

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace FormallySmooth

/-- Lemma 76.19.12: Let `S` be a scheme. Let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of algebraic spaces over `S`. Assume `f` is formally smooth. Then
the canonical transitivity sequence `0 ⟶ f^* Ω_{Y/Z} ⟶ Ω_{X/Z} ⟶ Ω_{X/Y} ⟶ 0`
of Lemma 76.7.8 is short exact. Here `f^* Ω_{Y/Z}` is
`(Modules.pullback f).obj (relativeDifferentials g)`, `Ω_{X/Z}` is
`relativeDifferentials (f ≫ g)`, and `Ω_{X/Y}` is `relativeDifferentials f`. -/
@[stacks 06BI]
theorem relativeDifferentialsTransitivity_shortExact
    {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
    [FormallySmooth f] :
    (complex f g).ShortExact :=
  sorry

end FormallySmooth

namespace Hom.Differentials.Transitivity

/-- For a formally smooth morphism `f : X ⟶ Y` of algebraic spaces, the first
arrow `baseChange` of the Lemma 76.7.8 transitivity sequence is a
monomorphism. -/
instance baseChange_mono {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [FormallySmooth f] :
    Mono (baseChange f g) :=
  sorry

end Hom.Differentials.Transitivity
end AlgebraicGeometry.AlgebraicSpace
