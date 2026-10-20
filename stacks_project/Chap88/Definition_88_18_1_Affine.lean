module

public import stacks_project.Chap88.Definition_88_20_1_Comparison
public import stacks_project.Chap88.Definition_88_18_1_Ring
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineRigSmooth

/-!
# Rig-smooth morphisms of affine formal algebraic spaces

A morphism of affine formal algebraic spaces corresponds to a rig-smooth map of
adic Noetherian topological rings when it is induced by a continuous
homomorphism `φ : A →+* B` that is rig-smooth as a homomorphism of adic
Noetherian topological rings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.RigSmooth :
  ∀ {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsAffine U]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [AlgebraicGeometry.FormalAlgebraicSpace.IsAffine V], (U ⟶ V) → Prop)
