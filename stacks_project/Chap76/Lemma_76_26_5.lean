/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap76.Lemma_76_26_3_CohenMacaulay

/-!
# Flat morphisms from Cohen–Macaulay algebraic spaces

A flat morphism of locally Noetherian algebraic spaces with Cohen–Macaulay
source is Cohen–Macaulay, and the étale local ring of the target at the image
of every geometric point of the source is Cohen–Macaulay.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace CohenMacaulay

/-- Lemma 76.26.5 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
locally Noetherian algebraic spaces over `S`. If `X` is Cohen–Macaulay, then `f`
is Cohen–Macaulay. -/
@[stacks 0E0Y]
theorem of_flat_of_source {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    (hX : hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u}) X) :
    CohenMacaulay f :=
  sorry

end CohenMacaulay

namespace etaleLocalRing

/-- Lemma 76.26.5 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a flat morphism of
locally Noetherian algebraic spaces over `S`. If `X` is Cohen–Macaulay, then
`𝒪_{Y, f(x̄)}` is Cohen–Macaulay for every geometric point `x̄` of `X`. -/
@[stacks 0E0Y]
theorem cohenMacaulayRing_of_flat_of_source {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [Flat f]
    (hX : hasEtaleLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u}) X)
    (xbar : GeometricPoint X) :
    CohenMacaulayRing (etaleLocalRing Y (xbar.map f)) :=
  sorry

end etaleLocalRing

end AlgebraicGeometry.AlgebraicSpace
