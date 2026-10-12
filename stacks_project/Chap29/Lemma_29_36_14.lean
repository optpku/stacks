/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Etale.StandardEtale
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 29.36.14: for a fixed affine open neighborhood `V` of `f x`, the morphism `f` is etale
at `x` if and only if an affine neighborhood `U` of `x` maps into `V` by a standard etale
coordinate-ring map. -/
@[stacks 02GT] #check
  (AlgebraicGeometry.Scheme.Hom.etaleAt_iff_exists_affineOpen_over_isStandardEtale :
    ∀ {X S : Scheme.{u}} {f : X ⟶ S} (x : X) (V : S.affineOpens),
      f x ∈ (V : S.Opens) →
        (f.EtaleAt x ↔
          ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
            f.IsStandardEtaleOver V U))
