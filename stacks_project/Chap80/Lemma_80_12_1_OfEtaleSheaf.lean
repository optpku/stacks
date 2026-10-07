module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Algebraic spaces from étale sheaves with étale-surjective atlases

An étale sheaf on `Sch/S` with representable diagonal and a representable, surjective,
and étale map from a scheme over `S` is an algebraic space: it is in particular an
fppf sheaf.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An étale sheaf on `Sch/S` with representable diagonal and a representable, surjective,
and étale atlas is an fppf sheaf. -/
theorem isSheaf_fppf_of_etale {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) F := sorry

/-- The given map `p` is a representable étale atlas that is locally surjective for the
étale topology. -/
theorem ofEtaleSheaf_isAtlas {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    (over (@Etale)).presheaf p ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The algebraic space over `S` obtained from an étale sheaf `F` with representable
diagonal together with a representable, surjective, and étale map `p : yoneda.obj U ⟶ F`
from a scheme `U` over `S`. -/
def ofEtaleSheaf {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    AlgebraicSpace S :=
  ofFunctor F (isSheaf_fppf_of_etale hF hΔ p hp) hΔ
    ⟨U, p, (ofEtaleSheaf_isAtlas hF hΔ p hp).1, (ofEtaleSheaf_isAtlas hF hΔ p hp).2⟩

/-- The functor of points of `ofEtaleSheaf hF hΔ p hp` is the given sheaf `F`. -/
@[simp]
theorem ofEtaleSheaf_functorOfPoints {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    (ofEtaleSheaf hF hΔ p hp).functorOfPoints = F := sorry

/-- The functor of points of `ofEtaleSheaf hF hΔ p hp` is a sheaf for the fppf topology. -/
theorem ofEtaleSheaf_isSheaf_fppf {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
      (ofEtaleSheaf hF hΔ p hp).functorOfPoints := sorry

/-- The diagonal of the functor of points of `ofEtaleSheaf hF hΔ p hp` is representable by
schemes over `S`. -/
theorem ofEtaleSheaf_representableDiagonal {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    yoneda.relativelyRepresentable (Limits.diag (ofEtaleSheaf hF hΔ p hp).functorOfPoints) :=
  sorry

/-- The algebraic space `ofEtaleSheaf hF hΔ p hp` is an fppf sheaf with representable diagonal
and a representable étale locally-surjective atlas. -/
theorem ofEtaleSheaf_spec {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.etaleTopology.over S) F)
    (hΔ : yoneda.relativelyRepresentable (Limits.diag F)) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@Etale ⊓ @Surjective)).presheaf p) :
    let X := ofEtaleSheaf hF hΔ p hp
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          (over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

end AlgebraicGeometry.AlgebraicSpace
