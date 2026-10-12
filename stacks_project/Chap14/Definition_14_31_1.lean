/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialSet.KanFibration
import StacksCheckRecall

/-!
@stack 08NU

# Definition 14.31.1 compatibility facade

Kan fibrations and Kan complexes are already the canonical morphism and object predicates of the
Quillen model structure on simplicial sets.  This file records the source terminology without
introducing a parallel predicate or reproving its horn-lifting characterization.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra Simplicial
open scoped SSet.modelCategoryQuillen

universe u

namespace SSet

open modelCategoryQuillen

variable {X Y : SSet.{u}} (f : X ⟶ Y)

/- Definition 14.31.1 (1): a Kan fibration is the canonical model-category predicate
`Fibration f`, characterized by the right lifting property against the family `J` of horn
inclusions. -/
@[stacks 08NU]
#check (modelCategoryQuillen.fibration_iff (f := f) : Fibration f ↔ J.rlp f)

/- The generators in `J` are precisely the horn inclusions used in the source definition. -/
@[stacks 08NU "explicit horn-lifting characterization of Kan fibrations"]
#check
  (J.rlp.iff_horn (f := f) :
    J.rlp f ↔ ∀ (n : ℕ) (i : Fin (n + 2)),
      HasLiftingProperty (horn (n + 1) i).ι f)

/- Definition 14.31.1 (2): a Kan complex is a fibrant simplicial set, equivalently one whose
canonical map to the terminal simplicial set is a Kan fibration. -/
@[stacks 08NU]
#check (KanComplex X)

@[stacks 08NU "Kan complexes via the terminal morphism"]
#check (isFibrant_iff X : KanComplex X ↔ Fibration (terminal.from X))

end SSet
