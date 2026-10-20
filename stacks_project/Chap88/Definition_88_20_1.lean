module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_20_1_Comparison
public import stacks_project.Chap88.Definition_88_20_1_Etale
public import stacks_project.Chap88.Definition_88_20_1_LocallyNoetherian
public import stacks_project.Chap88.Definition_88_20_1_Ring

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigEtale
import StacksCheckRecall

/-!
# Rig-étale morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

universe u

/- Definition 88.20.1: let `S` be a scheme, and let `f : X ⟶ Y` be a morphism
of locally Noetherian formal algebraic spaces over `S`. The morphism `f` is
rig-étale if every commutative square with affine formal algebraic spaces `U`,
`V` and étale maps `U ⟶ X`, `V ⟶ Y` representable by algebraic spaces has
`U ⟶ V` corresponding to a rig-étale map of adic Noetherian topological rings. -/
@[stacks 0AQM] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigEtale :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y], (X ⟶ Y) → Prop)
