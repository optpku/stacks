module

public import stacks_project.Chap67.Definition_67_40_1_Proper
public import stacks_project.Chap88.Definition_88_24_1_Modification
public import stacks_project.Chap88.Theorem_88_27_4

/-!
# Artin's theorem on dilatations

A formal modification of the completion of a locally Noetherian algebraic
space along a closed subset algebraizes uniquely to a proper morphism that is
an isomorphism over the complementary open.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Theorem 88.29.1 (1): let `S` be a scheme, let `X` be a locally Noetherian
algebraic space over `S`, and let `T ⊂ |X|` be a closed subset, with
`completionAlong X T` the formal completion of `X` along `T`. If
`f : X' ⟶ completionAlong X T` is a formal modification, then there exists a
proper morphism `g : Y ⟶ X` which is an isomorphism over the complement of
`T` in `X` and an isomorphism `e` of completions over `completionAlong X T`
whose composite recovers `f`. -/
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

/-- Theorem 88.29.1 (2): with notation as in Theorem 88.29.1 (1), a proper
morphism which is an isomorphism over the complement of `T` in `X` and whose
completion recovers the given formal modification is unique up to a unique
isomorphism over `X` whose completion intertwines `e₁` and `e₂`. -/
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
