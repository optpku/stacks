module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Algebraization
import StacksCheckRecall

/-!
# Artin's theorem on dilatations

A formal modification of the completion of a locally Noetherian algebraic
space along a closed subset algebraizes uniquely to a proper morphism that is
an isomorphism over the complementary open.
-/

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

universe u

/- Theorem 88.29.1 (1): every formal modification of the completion along
a closed subset algebraizes to a proper morphism which is an isomorphism
over the complementary open. -/
@[stacks 0GDU] #check (AlgebraicGeometry.AlgebraicSpace.exists_proper_of_formalModification :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X))
    {X' : (Over S)ᵒᵖ ⥤ Type u} [FormalAlgebraicSpace.IsFormalAlgebraicSpace X']
    [FormalAlgebraicSpace.IsLocallyNoetherian X']
    (f : X' ⟶ completionAlong X T)
    [FormalAlgebraicSpace.LocallyOfFiniteType f]
    [FormalAlgebraicSpace.FormalModification f],
    ∃ (Y : AlgebraicSpace S) (g : Y ⟶ X)
      (e : completionAlong Y (T.preimage (Points.continuous_map g)) ≅ X'),
      AlgebraicSpace.Proper g ∧
        IsIso (openInverseImageTo g (openComplementι X T)) ∧
        e.hom ≫ f = completionAlong.map g T)

/- Theorem 88.29.1 (2): algebraizations of a formal modification are unique
up to a unique isomorphism over the target compatible with completion. -/
@[stacks 0GDU] #check (AlgebraicGeometry.AlgebraicSpace.uniqueIso_proper_of_formalModification :
  ∀ {S : Scheme.{u}}
    {X Y₁ Y₂ : AlgebraicSpace S} [IsLocallyNoetherian X]
    (T : Closeds (Points X)) (g₁ : Y₁ ⟶ X) (g₂ : Y₂ ⟶ X)
    [AlgebraicSpace.Proper g₁] [AlgebraicSpace.Proper g₂]
    [IsIso (openInverseImageTo g₁ (openComplementι X T))]
    [IsIso (openInverseImageTo g₂ (openComplementι X T))]
    {X' : (Over S)ᵒᵖ ⥤ Type u} [FormalAlgebraicSpace.IsFormalAlgebraicSpace X']
    [FormalAlgebraicSpace.IsLocallyNoetherian X']
    (f : X' ⟶ completionAlong X T)
    [FormalAlgebraicSpace.LocallyOfFiniteType f]
    [FormalAlgebraicSpace.FormalModification f]
    (e₁ : completionAlong Y₁ (T.preimage (Points.continuous_map g₁)) ≅ X')
    (e₂ : completionAlong Y₂ (T.preimage (Points.continuous_map g₂)) ≅ X')
    (he₁ : e₁.hom ≫ f = completionAlong.map g₁ T)
    (he₂ : e₂.hom ≫ f = completionAlong.map g₂ T),
    ∃! φ : Y₁ ≅ Y₂, ∃ h : φ.hom ≫ g₂ = g₁,
      completionAlong.mapOver T (Over.homMk φ.hom h : Over.mk g₁ ⟶ Over.mk g₂) ≫ e₂.hom = e₁.hom)
