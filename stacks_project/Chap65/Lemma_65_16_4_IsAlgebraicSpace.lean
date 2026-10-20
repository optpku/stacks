module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Unbundled algebraic-space predicate

A functor of points on schemes over `S` is an algebraic space when it satisfies the
three conditions of `AlgebraicSpace`: fppf descent, representable diagonal, and a
representable étale locally-surjective atlas.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (IsAlgebraicSpace : ∀ {S : Scheme.{u}}, ((Over S)ᵒᵖ ⥤ Type u) → Prop)

#check (instIsAlgebraicSpace_functorOfPoints :
  ∀ {S : Scheme.{u}} (X : AlgebraicSpace S), IsAlgebraicSpace X.functorOfPoints)

#check (ofIsAlgebraicSpace :
  ∀ {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) [IsAlgebraicSpace F], AlgebraicSpace S)

#check (ofIsAlgebraicSpace_functorOfPoints :
  ∀ {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u) [IsAlgebraicSpace F],
    (ofIsAlgebraicSpace F).functorOfPoints = F)

#check (isAlgebraicSpace_iff : ∀ {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u),
  IsAlgebraicSpace F ↔
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F ∧
      yoneda.relativelyRepresentable (Limits.diag F) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
          MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p)

end AlgebraicGeometry.AlgebraicSpace
