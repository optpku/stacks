module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSurjective
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Definition 88.21.1: a locally finite type morphism between locally Noetherian
formal algebraic spaces is rig-surjective if every adic complete-DVR test map
lifts after an extension of complete discrete valuation rings. -/
@[stacks 0AQQ] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigSurjective :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [LocallyOfFiniteType f], Prop)
