module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigFlat
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
import StacksCheckRecall

/-!
# Rig-flat morphisms of locally Noetherian formal algebraic spaces
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 88.16.1. A morphism of locally Noetherian formal algebraic spaces
is rig-flat when every commutative affine étale chart square has its horizontal
arrow induced by a rig-flat homomorphism of adic Noetherian topological rings. -/
@[stacks 0GGX] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigFlat :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsLocallyNoetherian X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsLocallyNoetherian Y], (X ⟶ Y) → Prop)
