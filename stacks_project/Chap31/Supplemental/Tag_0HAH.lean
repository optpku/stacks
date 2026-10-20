module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Rank.Pullback
import StacksCheckRecall

/-!
# Lemma [Stacks 0HAH]

The cardinal generic rank of a quasi-coherent module on an integral scheme is
invariant under pullback along a dominant morphism of integral schemes.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma [Stacks 0HAH]
Dominant pullback between integral schemes preserves the cardinal generic rank
of every quasi-coherent module.
-/
@[stacks 0HAH] #check (AlgebraicGeometry.Scheme.Modules.pullback_rank_eq :
  ∀ {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsDominant f] (𝒢 : Y.Modules) [𝒢.IsQuasicoherent],
    Module.rank Y.functionField (RingedSpace.stalkModuleCat 𝒢 (genericPoint Y)) =
      Module.rank X.functionField
        (RingedSpace.stalkModuleCat
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj 𝒢) (genericPoint X)))
