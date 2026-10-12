/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.PseudoCoherent.Relative.Module
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}}

/- Lemma 37.59.11 (1): every module over the source of a locally finite type morphism is
`m`-pseudo-coherent relative to the target for `m > 0`. -/
@[stacks 09UM]
#check
  (AlgebraicGeometry.Scheme.Modules.isMPseudoCoherentOver_of_pos :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules) (m : ℤ), 0 < m → F.IsMPseudoCoherentOver f m)

/- Lemma 37.59.11 (2): relative `0`-pseudo-coherence of a module is equivalent to finite
type. -/
@[stacks 09UM]
#check
  (AlgebraicGeometry.Scheme.Modules.isMPseudoCoherentOver_zero_iff :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules), F.IsMPseudoCoherentOver f 0 ↔ F.IsFiniteType)

/- Lemma 37.59.11 (3): relative `(-1)`-pseudo-coherence of a module is equivalent to
quasi-coherence together with relative finite presentation. -/
@[stacks 09UM]
#check
  (AlgebraicGeometry.Scheme.Modules.isMPseudoCoherentOver_minusOne_iff :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
      (F : X.Modules),
        F.IsMPseudoCoherentOver f (-1) ↔ F.IsQuasicoherent ∧ F.IsFinitePresentationOver f)

end AlgebraicGeometry.Scheme.Modules
