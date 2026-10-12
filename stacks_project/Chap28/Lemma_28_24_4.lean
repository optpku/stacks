/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ideal.Pushforward
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 28.24.4: for a quasi-compact and quasi-separated morphism `f : X ⟶ Y`, pushforward
identifies, sectionwise on every open, the subsheaf of a quasi-coherent module annihilated by the
pulled-back finite type ideal sheaf with the subsheaf annihilated by the original ideal sheaf. -/
@[stacks 07ZN]
#check (AlgebraicGeometry.Scheme.Modules.range_pushforward_idealTorsionSubsheafι_app_eq :
  ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (I : Y.IdealSheafData)
    [((Subobject.underlying.obj I.toSubobject : Y.Modules).IsFiniteType)]
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (U : Y.Opens),
    Set.range (((pushforward f).map
        (idealTorsionSubsheafι (I.comap f) ℱ)).app U) =
      Set.range ((idealTorsionSubsheafι I ((pushforward f).obj ℱ)).app U))

end AlgebraicGeometry.Scheme.Modules
