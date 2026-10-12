/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Module.Reflexive.Pullback

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}
variable [IsIntegral X] [IsIntegral Y]
variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
variable (f : X ⟶ Y) [Flat f]
variable (G : Y.Modules) [G.IsCoherent] [IsReflexive G]

/- Lemma 31.12.6 (1): for a flat morphism `f : X ⟶ Y` of integral locally Noetherian
schemes and a coherent reflexive module sheaf `G` on `Y`, `(pullback f).obj G` is coherent. -/
@[stacks 0EBF] #check
  (AlgebraicGeometry.Scheme.Modules.pullback_isCoherent f G :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj G).IsCoherent)

/- Lemma 31.12.6 (2): for a flat morphism `f : X ⟶ Y` of integral locally Noetherian
schemes and a coherent reflexive module sheaf `G` on `Y`, `(pullback f).obj G` is reflexive. -/
@[stacks 0EBF] #check
  (AlgebraicGeometry.Scheme.Modules.pullback_isReflexive_of_flat f G :
    IsReflexive ((AlgebraicGeometry.Scheme.Modules.pullback f).obj G))

end AlgebraicGeometry.Scheme.Modules
