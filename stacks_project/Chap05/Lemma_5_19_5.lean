/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Inseparable
import StacksCheckRecall

@[expose] public section

universe u v w

variable {X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/- Lemma 5.19.5 (1): specialization lifting is closed under composition; the
source continuity assumptions are not required by Mathlib's owner. -/
@[stacks 0064 "composition of specialization-lifting continuous maps"]
#check fun {f : X → Y} {g : Y → Z} (_ : Continuous f) (_ : Continuous g)
    (hf : SpecializingMap f) (hg : SpecializingMap g) ↦ hf.comp hg

/- Lemma 5.19.5 (2): generalization lifting is closed under composition; the
source continuity assumptions are not required by Mathlib's owner. -/
@[stacks 0064 "composition of generalization-lifting continuous maps"]
#check fun {f : X → Y} {g : Y → Z} (_ : Continuous f) (_ : Continuous g)
    (hf : GeneralizingMap f) (hg : GeneralizingMap g) ↦ hf.comp hg
