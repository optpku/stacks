module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative.Pushforward
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 37.58.4: for a finite morphism of schemes locally of finite type over a base
scheme, a quasi-coherent module is of finite presentation relative to the base if and only if
its pushforward is. -/
@[stacks 09T9]
#check
  (AlgebraicGeometry.Scheme.Modules.isFinitePresentationOver_iff_pushforward_of_isFinite :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S) [IsFinite f]
      [LocallyOfFiniteType g] (F : X.Modules) [F.IsQuasicoherent],
      F.IsFinitePresentationOver (f ≫ g) ↔
        ((Scheme.Modules.pushforward f).obj F).IsFinitePresentationOver g)
