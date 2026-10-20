module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.Definition_88_18_1_Affine
public import stacks_project.Chap88.Definition_88_20_1_Etale
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.RigSmooth
import StacksCheckRecall

/-!
# Rig-smooth morphisms of locally Noetherian formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.FormalAlgebraicSpace

noncomputable section

universe u

/- Definition 88.18.1: a morphism of locally Noetherian formal algebraic spaces
is rig-smooth when every affine étale chart square has a rig-smooth horizontal
arrow induced by a homomorphism of adic Noetherian topological rings. -/
@[stacks 0GCP] #check (AlgebraicGeometry.FormalAlgebraicSpace.RigSmooth :
  ∀ {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace Y]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsLocallyNoetherian X]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsLocallyNoetherian Y], (X ⟶ Y) → Prop)
