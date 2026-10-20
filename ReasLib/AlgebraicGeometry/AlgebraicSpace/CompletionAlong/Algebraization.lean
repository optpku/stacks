module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Equivalence
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.FormalModification
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CompletionAlong.Map
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Open.Complement
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.FormalModification

/-!
# Algebraization of formal modifications

Formal modifications of completions along closed subsets of locally Noetherian
algebraic spaces algebraize uniquely to proper morphisms that are isomorphisms
over the complementary open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A formal modification of the completion of a locally Noetherian algebraic
space along a closed subset is the completion of a proper morphism which is an
isomorphism over the complementary open. -/
@[stacks 0GDU]
theorem exists_proper_of_formalModification {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (T : Closeds (Points X))
    {X' : (Over S)ᵒᵖ ⥤ Type u} [FormalAlgebraicSpace.IsFormalAlgebraicSpace X']
    [FormalAlgebraicSpace.IsLocallyNoetherian X']
    (f : X' ⟶ completionAlong X T)
    [FormalAlgebraicSpace.LocallyOfFiniteType f]
    [FormalAlgebraicSpace.FormalModification f] :
    ∃ (Y : AlgebraicSpace S) (g : Y ⟶ X)
      (e : completionAlong Y (T.preimage (Points.continuous_map g)) ≅ X'),
      AlgebraicSpace.Proper g ∧
        IsIso (openInverseImageTo g (openComplementι X T)) ∧
        e.hom ≫ f = completionAlong.map g T :=
  sorry

/-- Two proper morphisms to a locally Noetherian algebraic space which are
isomorphisms over the complement of a closed subset and recover the same formal
modification on completion are uniquely isomorphic over the target, compatibly
with their specified completion isomorphisms. -/
@[stacks 0GDU]
theorem uniqueIso_proper_of_formalModification {S : Scheme.{u}}
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
    (he₂ : e₂.hom ≫ f = completionAlong.map g₂ T) :
    ∃! φ : Y₁ ≅ Y₂, ∃ h : φ.hom ≫ g₂ = g₁,
      completionAlong.mapOver T (Over.homMk φ.hom h : Over.mk g₁ ⟶ Over.mk g₂) ≫ e₂.hom = e₁.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
