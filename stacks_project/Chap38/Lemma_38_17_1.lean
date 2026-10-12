/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.Proper
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.17.1 (1): a finite type quasicoherent module whose support is proper over
the base is universally pure relative to the base. -/
@[stacks 05K3] #check
  (AlgebraicGeometry.Scheme.Modules.isUniversallyPureOver_of_hasProperSupportOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [f.FiniteType]
      (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent]
      [HasProperSupportOver f F],
      F.IsUniversallyPureOver f)

/- Lemma 38.17.1 (2): a finite type quasicoherent module on the source of a proper
morphism is universally pure relative to the target. -/
@[stacks 05K3] #check
  (AlgebraicGeometry.Scheme.Modules.isUniversallyPureOver_of_isProper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
      (F : X.Modules) [F.IsFiniteType] [F.IsQuasicoherent],
      F.IsUniversallyPureOver f)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

/- Lemma 38.17.1 (3): the source of a proper morphism is universally pure relative
to the target, via its structure sheaf. -/
@[stacks 05K3] #check
  (AlgebraicGeometry.Scheme.isUniversallyPureOver_of_isProper :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f],
      Modules.IsUniversallyPureOver
        (SheafOfModules.unit X.ringCatSheaf : X.Modules) f)

end AlgebraicGeometry.Scheme
