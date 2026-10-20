module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.Scheme.Sites.RepresentableSheaf

/-!
# Algebraic spaces from representable transformations

A functor admitting a relatively representable transformation to an algebraic space satisfies the defining conditions for an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A relatively representable transformation to an algebraic space gives the defining conditions for its source functor. -/
theorem ofRelativelyRepresentable_spec {S : Scheme.{u}} {F : AlgebraicSpace S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (a : G ⟶ F.functorOfPoints)
    (ha : yoneda.relativelyRepresentable a) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) G ∧
      yoneda.relativelyRepresentable (Limits.diag G) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ G),
          MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := by
  refine ⟨AlgebraicGeometry.isSheaf_fppfTopology_over_of_relativelyRepresentable a ha F.isSheaf, ?_⟩
  sorry

/-- The algebraic space constructed from a relatively representable transformation has source functor `G`. -/
def ofRelativelyRepresentable {S : Scheme.{u}} {F : AlgebraicSpace S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (a : G ⟶ F.functorOfPoints)
    (ha : yoneda.relativelyRepresentable a) : AlgebraicSpace S :=
  ofFunctor G (ofRelativelyRepresentable_spec a ha).1
    (ofRelativelyRepresentable_spec a ha).2.1
    (ofRelativelyRepresentable_spec a ha).2.2

/-- The functor of points of the constructed algebraic space is definitionally the source functor. -/
@[simp]
theorem ofRelativelyRepresentable_functorOfPoints {S : Scheme.{u}} {F : AlgebraicSpace S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (a : G ⟶ F.functorOfPoints)
    (ha : yoneda.relativelyRepresentable a) :
    (ofRelativelyRepresentable a ha).functorOfPoints = G :=
  rfl

/-- The relatively representable transformation induces a morphism of algebraic spaces. -/
def ofRelativelyRepresentable_hom {S : Scheme.{u}} {F : AlgebraicSpace S}
    {G : (Over S)ᵒᵖ ⥤ Type u} (a : G ⟶ F.functorOfPoints)
    (ha : yoneda.relativelyRepresentable a) :
    ofRelativelyRepresentable a ha ⟶ F :=
  a

/-- The induced morphism of algebraic spaces is represented by the original transformation. -/
theorem ofRelativelyRepresentable_hom_relativelyRepresentable {S : Scheme.{u}}
    {F : AlgebraicSpace S} {G : (Over S)ᵒᵖ ⥤ Type u} (a : G ⟶ F.functorOfPoints)
    (ha : yoneda.relativelyRepresentable a) :
    yoneda.relativelyRepresentable (ofRelativelyRepresentable_hom a ha) :=
  ha

end AlgebraicGeometry.AlgebraicSpace
