/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.CentralSimple.BrauerGroup.Group
import StacksCheckRecall

universe u v

@[expose] public section

/- Definition 59.61.3: Two finite central simple algebras over a field are
similar, or equivalent, when positive-size matrix algebras over them are
isomorphic as algebras over the field. -/

@[stacks 03R3] #check (BrauerGroup.IsBrauerEquivalent :
  ∀ {K : Type u} [Field K], CSA.{u, v} K → CSA.{u, v} K → Prop)

end
