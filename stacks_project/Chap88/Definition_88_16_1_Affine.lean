module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffineRigFlat
public import stacks_project.Chap88.Definition_88_20_1_Comparison
public import stacks_project.Chap88.Lemma_88_15_8_RigFlat

/-!
# Rig-flat morphisms of affine formal algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- A morphism of affine formal algebraic spaces is rig-flat when it is induced
by a rig-flat continuous homomorphism of adic Noetherian topological rings. -/
#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.RigFlat :
  ∀ {S : Scheme.{u}} {U V : (Over S)ᵒᵖ ⥤ Type u}
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace U]
    [FormalAlgebraicSpace.IsAffine U]
    [FormalAlgebraicSpace.IsFormalAlgebraicSpace V]
    [FormalAlgebraicSpace.IsAffine V], (U ⟶ V) → Prop)
