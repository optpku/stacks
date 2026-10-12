/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Fpqc.Stability
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Limits

universe u v w

/- Lemma 34.9.8 (1): an isomorphism gives a singleton fpqc covering. -/
@[stacks 022D]
#check (AlgebraicGeometry.Scheme.fpqcCovering_singleton_of_isIso :
  ∀ {T T' : AlgebraicGeometry.Scheme.{u}} (f : T' ⟶ T) [IsIso f],
    AlgebraicGeometry.Scheme.FpqcCovering
      (fun _ : Unit ↦ CategoryTheory.Over.mk f))

/- Lemma 34.9.8 (2): indexed composition preserves fpqc coverings. -/
@[stacks 022D]
#check (AlgebraicGeometry.Scheme.fpqcCovering_comp :
  ∀ {T : AlgebraicGeometry.Scheme.{u}} {ι : Type v} {κ : ι → Type w}
    (X : ι → CategoryTheory.Over T)
    (Y : (i : ι) → κ i → CategoryTheory.Over (X i).left)
    (hX : AlgebraicGeometry.Scheme.FpqcCovering X)
    (hY : ∀ i : ι, AlgebraicGeometry.Scheme.FpqcCovering (Y i)),
    AlgebraicGeometry.Scheme.FpqcCovering (fun p : Sigma κ ↦
      CategoryTheory.Over.mk ((Y p.1 p.2).hom ≫ (X p.1).hom)))

/- Lemma 34.9.8 (3): pullback preserves fpqc coverings. -/
@[stacks 022D]
#check (AlgebraicGeometry.Scheme.fpqcCovering_pullback :
  ∀ {T T' : AlgebraicGeometry.Scheme.{u}} {ι : Type v}
    (X : ι → CategoryTheory.Over T)
    (hX : AlgebraicGeometry.Scheme.FpqcCovering X) (f : T' ⟶ T),
    AlgebraicGeometry.Scheme.FpqcCovering (fun i : ι ↦
      CategoryTheory.Over.mk (pullback.snd (X i).hom f)))
