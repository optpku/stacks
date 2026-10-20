module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative.BaseChange
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 37.58.6: pullback along a locally finitely presented morphism preserves
relative finite presentation of a quasi-coherent module. -/
@[stacks 09TB] #check
  (AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver.pullback :
    ∀ {X Y S : Scheme.{u}} {g : Y ⟶ S} [LocallyOfFiniteType g]
      {G : Y.Modules} [G.IsQuasicoherent],
      G.IsFinitePresentationOver g → ∀ (f : X ⟶ Y) [LocallyOfFinitePresentation f],
        ((Scheme.Modules.pullback f).obj G).IsFinitePresentationOver (f ≫ g))
