module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CompletelyDecomposed

@[expose] public section

open CategoryTheory

universe u v

/- A family of scheme morphisms is completely decomposed precisely when every canonical
residue-field point of the target lifts through a member of the family. -/
#check (AlgebraicGeometry.CompletelyDecomposedFamily :
  {I : Type v} → {T : AlgebraicGeometry.Scheme.{u}} →
    (X : I → AlgebraicGeometry.Scheme.{u}) → (∀ i, X i ⟶ T) → Prop)

/- A scheme morphism is completely decomposed when its singleton family is completely
decomposed. -/
#check (AlgebraicGeometry.Scheme.Hom.CompletelyDecomposed :
  {X T : AlgebraicGeometry.Scheme.{u}} → (X ⟶ T) → Prop)
