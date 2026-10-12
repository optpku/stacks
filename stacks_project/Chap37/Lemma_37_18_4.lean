/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Support.Flat
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 37.18.4: if a finite-type quasicoherent module is flat over an irreducible
base and the support of its generic fiber has dimension at most `r`, then the support
of every fiber has dimension at most `r`. -/
@[stacks 0H3X] #check
  (AlgebraicGeometry.Scheme.Modules.topologicalKrullDim_moduleSupport_fiber_le :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)
      [LocallyOfFiniteType f] [ℱ.IsQuasicoherent] [ℱ.IsFiniteType]
      [IrreducibleSpace S] (hflat : flatOver ℱ f) {r : ℕ}
      (hη : topologicalKrullDim
        (moduleSupport ((Scheme.Modules.pullback (f.fiberι (genericPoint S))).obj ℱ)) ≤
          (r : WithBot ℕ∞)) (s : S),
      topologicalKrullDim
        (moduleSupport ((Scheme.Modules.pullback (f.fiberι s)).obj ℱ)) ≤
          (r : WithBot ℕ∞))

end AlgebraicGeometry.Scheme.Modules
