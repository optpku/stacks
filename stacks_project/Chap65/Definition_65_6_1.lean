module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 65.6.1: an algebraic space over a scheme `S` is a presheaf
`F : (Over S)ᵒᵖ ⥤ Type` that is an fppf sheaf, whose diagonal `F ⟶ F ⨯ F` is
representable, and that admits a scheme `U` over `S` with a map
`yoneda.obj U ⟶ F` which is surjective and étale. -/
@[stacks 025Y] #check (AlgebraicGeometry.AlgebraicSpace.IsAlgebraicSpace :
  {S : AlgebraicGeometry.Scheme.{u}} → (CategoryTheory.Over S)ᵒᵖ ⥤ Type u → Prop)

/- The three defining conditions, with the atlas stated literally as a representable
surjective étale morphism from a scheme. -/
#check (AlgebraicGeometry.AlgebraicSpace.isAlgebraicSpace_iff_etale_surjective :
  ∀ {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u),
    AlgebraicSpace.IsAlgebraicSpace F ↔
      Presheaf.IsSheaf (Scheme.fppfTopology.over S) F ∧
        yoneda.relativelyRepresentable (Limits.diag F) ∧
          ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
            MorphismProperty.presheaf (MorphismProperty.over (@Etale ⊓ @Surjective)) p)
