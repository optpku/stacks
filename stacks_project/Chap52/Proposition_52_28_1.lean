/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Proposition_52_28_1_Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology

/- Proposition 52.28.1: for a proper scheme `P` over a field, an ample invertible
module `L` with section `s`, a coherent module `F`, and the inverse system of the
cohomology modules of the infinitesimal neighborhoods `Qₙ` of `Q = Z(s)`, if
`depth(Fₚ) + dim(closure {p}) > σ` away from `Q`, then the canonical comparison
`Hⁱ(P, F) ⟶ lim Hⁱ(Qₙ, Fₙ)` is an isomorphism for `0 ≤ i < σ`; the
neighborhood terms are `Scheme.Hom.cohomology (toAmbient n ≫ P.hom)` of the
pulled-back module, transported to the ambient pushforward tower by the canonical
stage identifications. -/
@[stacks 0EL1] #check
  (AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology.comparison_isIso_of_depth :
    ∀ {k : Type u} [Field k] (P : SchemeOverField k) [IsProper P.hom]
    (L : P.left.Modules) [L.Invertible] [L.IsAmple]
    (s : L.sections) (F : P.left.Modules) [F.IsCoherent]
    (σ : ℤ) (i : ℕ)
    (hdepth : ∀ p : P.left, p ∉ Set.range (Scheme.zeroSchemeι L s) →
      ((WithTop.map Int.ofNat
          (moduleDepth (SchemeOverField.stalkRing P p)
            (RingedSpace.stalkModuleCat F p)) : WithTop ℤ) : EInt) +
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (closure ({p} : Set P.left))) >
        (σ : EInt))
    (his : (i : ℤ) < σ),
    IsIso (AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology.comparison
      P L s F i))

end AlgebraicGeometry.Scheme.InfinitesimalNeighbourhoodCohomology
