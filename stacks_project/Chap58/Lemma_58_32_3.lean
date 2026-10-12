/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AffineSpace.EtaleExtension
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AffineSpace

/- Lemma 58.32.3: a finite étale morphism to a closed subscheme of affine space in positive
characteristic extends to a finite étale morphism whose pullback contains it as a clopen subscheme. -/
@[stacks 0G1H]
#check (AlgebraicGeometry.AffineSpace.existsFiniteEtaleClopenExtension :
    ∀ {k : Type u} [Field k] (p n : ℕ) [CharP k p] (h_positiveChar : 0 < p)
    {Z Y : Scheme.{u}}
    (i : Z ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k))) [IsClosedImmersion i]
    (g : Y ⟶ Z) [IsFinite g] [Etale g],
      ∃ (U : Scheme.{u})
        (f : U ⟶ 𝔸(ULift.{u} (Fin n); Spec (CommRingCat.of.{u} k))),
        (IsFinite f ∧ Etale f) ∧
          ∃ (j : Y ⟶ pullback f i),
            IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd f i = g)

end AlgebraicGeometry.AffineSpace
