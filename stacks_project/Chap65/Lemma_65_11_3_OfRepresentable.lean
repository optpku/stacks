module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OfRepresentable
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Algebraic spaces from representable maps

A functor that admits a representable morphism to an algebraic space is itself an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (ofRelativelyRepresentable :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → {G : (Over S)ᵒᵖ ⥤ Type u} →
    (a : G ⟶ F.functorOfPoints) → yoneda.relativelyRepresentable a → AlgebraicSpace S)

#check (ofRelativelyRepresentable_functorOfPoints :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → {G : (Over S)ᵒᵖ ⥤ Type u} →
    (a : G ⟶ F.functorOfPoints) → (ha : yoneda.relativelyRepresentable a) →
      (ofRelativelyRepresentable a ha).functorOfPoints = G)

#check (ofRelativelyRepresentable_hom :
  {S : Scheme.{u}} → {F : AlgebraicSpace S} → {G : (Over S)ᵒᵖ ⥤ Type u} →
    (a : G ⟶ F.functorOfPoints) → (ha : yoneda.relativelyRepresentable a) →
      ofRelativelyRepresentable a ha ⟶ F)

end AlgebraicGeometry.AlgebraicSpace
