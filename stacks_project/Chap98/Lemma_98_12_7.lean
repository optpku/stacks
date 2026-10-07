module

public import ReasLib.CategoryTheory.Fibered.Groupoids.Base
public import ReasLib.RingTheory.Regular.GRing
public import stacks_project.Chap97.«97_5_0_1_OnObjects»
public import stacks_project.Chap98.Definition_98_9_4_Effective
public import stacks_project.Chap98.Lemma_98_12_7_Approximate
import Mathlib.Tactic.CrossRefAttribute

/-!
# Approximating a versal effective formal object by a finite type versal object

If `S` is locally Noetherian, `ξ` is a versal effective formal object of a
category fibred in groupoids `X` over `(Sch/S)_fppf` whose first stage lies over
`Spec(k) ⟶ S` with image `s`, `𝒪_{S,s}` is a G-ring, and the structure morphism
of `X` is limit preserving on objects, then `ξ` is approximated by an object
over a finite type scheme `U ⟶ S`, versal at a finite type point.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open AlgebraicGeometry.Groupoids.Hom
open FiberedCategoryOver.Groupoids

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- Lemma 98.12.7: let `S` be a locally Noetherian scheme, let `X` be a category
fibred in groupoids over `(Sch/S)_fppf`, and let `ξ` be a formal object of `X`
whose first stage lies over `Spec(k) ⟶ S` with image `s`. Assume `ξ` is versal,
`ξ` is effective, `𝒪_{S,s}` is a G-ring, and the structure morphism of `X` is
limit preserving on objects. Then there exist a finite type morphism `U ⟶ S`,
a finite type point `u0 ∈ U` with residue field `k`, and an object `x` of `X`
over `U` such that `x` is versal at `u0` and
`x` restricted to `Spec(𝒪_{U,u0} ⧸ m_{u0}^n)` is isomorphic to `ξ_n` for every
`n`. Lean stage `n` is the source object `ξ_{n+1}` over
`Spec(R ⧸ m^{n+1})`. -/
@[stacks 07XH]
theorem nonempty_approximateVersal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S}
    [LimitPreservingOnObjects (baseProjection.{u + 1, u, u + 1} X)]
    (ξ : FormalObject X) (s : S)
    (hs : ξ.base.toS (closedPoint ξ.base.carrier) = s)
    [IsGRing (S.presheaf.stalk s)] [FormalObject.IsEffective ξ]
    (h_versal : FormalObject.IsVersalOnObjects ξ) :
    Nonempty (ApproximateVersal ξ) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
