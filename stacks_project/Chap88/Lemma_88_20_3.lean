module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Lemma 88.20.3: A rig-étale morphism of locally Noetherian formal algebraic
spaces is locally of finite type. -/
@[stacks 0AQN] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigEtale.toLocallyOfFiniteType :
    ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (f : X ⟶ Y) [RigEtale f], LocallyOfFiniteType f)
