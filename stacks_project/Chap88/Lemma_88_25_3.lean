module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Factorization
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Lemma 88.25.3: A morphism from a locally Noetherian algebraic space
factors through a locally finite-type monomorphism if it factors through it
on the open complement of a closed subset and on its completion. -/
@[stacks 0AR6] #check (AlgebraicGeometry.AlgebraicSpace.completionAlong.exists_factorThrough :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X ⟶ Y) (g : Z ⟶ Y)
    [Mono g] [LocallyOfFiniteType g]
    (h_open : ∃ h : openComplementAlong X T ⟶ Z, h ≫ g = openComplementι X T ≫ f)
    (h_completion : ∃ h : completionAlong X T ⟶ Z.functorOfPoints,
      h ≫ g = completionAlong.ι X T ≫ f),
    ∃ h : X ⟶ Z, h ≫ g = f)

#check (AlgebraicGeometry.AlgebraicSpace.completionAlong.existsUnique_factorThrough :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X)) (f : X ⟶ Y) (g : Z ⟶ Y)
    [Mono g] [LocallyOfFiniteType g]
    (h_open : ∃ h : openComplementAlong X T ⟶ Z, h ≫ g = openComplementι X T ≫ f)
    (h_completion : ∃ h : completionAlong X T ⟶ Z.functorOfPoints,
      h ≫ g = completionAlong.ι X T ≫ f),
    ∃! h : X ⟶ Z, h ≫ g = f)
