module

public import ReasLib.AlgebraicGeometry.WeilCohomology.PreWeil.ClosedImmersion
import StacksCheckRecall

@[expose] public section

universe u v w x y z

open AlgebraicGeometry CategoryTheory

namespace WeilCohomology

variable {k : Type u} [Field k]
variable {F : Type v} [Field F] [CharZero F]
variable {TateLine : Type x} [AddCommGroup TateLine] [Module F TateLine]
variable {V : Type w} [Category.{z} V]
variable {dimension : V → ℕ} {product : V → V → V}
variable {fst : ∀ X Y, product X Y ⟶ X} {snd : ∀ X Y, product X Y ⟶ Y}
variable {point : V} {CH : V → Type y} [∀ X, CommRing (CH X)]
variable {CHgrade : ∀ X, ℤ → Submodule ℤ (CH X)} [∀ X, GradedAlgebra (CHgrade X)]
variable {cyclePullback : ∀ {X Y : V}, (X ⟶ Y) → CHgrade Y →ₐᵍ[ℤ] CHgrade X}
variable {cyclePushforward : ∀ {X Y : V}, (X ⟶ Y) → CH X →+ CH Y}
variable {pointCycle : CHgrade point 0} {H Picard : V → Type x}
variable [∀ X, Ring (H X)] [∀ X, Algebra F (H X)] [∀ X, AddCommGroup (Picard X)]

/- Lemma 45.14.11: data (D0), (D1), and (D2') satisfying axioms (A1)–(A7),
compatibility of the cycle-class map with pushforward follows from the identity
i_*(1) = γ([Z]) for every closed immersion of nonempty equidimensional objects. -/
@[stacks 0FIP] #check
  (WeilCohomology.SchemePreWeilTheory.cycleClass_pushforward_of_closedImmersion :
    ∀ (T : SchemePreWeilTheory k F TateLine V dimension product fst snd point CH CHgrade
      cyclePullback cyclePushforward pointCycle H Picard)
      (h_closed : ∀ {Z X : V} {d e : ℕ}
        (hZ : T.IsNonemptyEquidimensional Z d)
        (hX : T.IsNonemptyEquidimensional X e) (i : Z ⟶ X)
        [IsClosedImmersion (T.scheme.map i).left],
        T.pushforward hZ hX i (1 : H Z) =
          T.cycleClass X (cyclePushforward i (1 : CHgrade Z 0)))
      {X Y : V} {d e : ℕ} (hX : T.IsNonemptyEquidimensional X d)
      (hY : T.IsNonemptyEquidimensional Y e) (f : X ⟶ Y) (alpha : CH X),
      T.pushforward hX hY f (T.cycleClass X alpha) =
        T.cycleClass Y (cyclePushforward f alpha))

end WeilCohomology
