module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Algebraic spaces from representable étale-surjective atlases

An fppf sheaf on `Sch/S` equipped with a representable, surjective, and étale map from a
scheme over `S` is an algebraic space: the representable-diagonal axiom is automatic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `S` obtained from an fppf sheaf `F` together with a representable,
surjective, and étale map `p : yoneda.obj U ⟶ F` from a scheme `U` over `S`. -/
def ofEtaleSurjective {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    AlgebraicSpace S :=
  ofFunctor F hF sorry ⟨U, p, sorry, sorry⟩

/-- The functor of points of `ofEtaleSurjective hF p hp` is the given sheaf `F`. -/
@[simp]
theorem ofEtaleSurjective_functorOfPoints {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    (ofEtaleSurjective hF p hp).functorOfPoints = F := sorry

/-- The algebraic space `ofEtaleSurjective hF p hp` is an fppf sheaf with representable diagonal
and a representable étale locally-surjective atlas. -/
theorem ofEtaleSurjective_spec {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    let X := ofEtaleSurjective hF p hp
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          (over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The diagonal of the functor of points of `ofEtaleSurjective hF p hp` is representable by
schemes over `S`. -/
theorem ofEtaleSurjective_representableDiagonal {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    yoneda.relativelyRepresentable (Limits.diag (ofEtaleSurjective hF p hp).functorOfPoints) :=
  sorry

/-- The given map `p` is a representable étale atlas of `ofEtaleSurjective hF p hp` that is
locally surjective for the étale topology. -/
theorem ofEtaleSurjective_isAtlas {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    (over (@Etale)).presheaf p ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

end AlgebraicGeometry.AlgebraicSpace
