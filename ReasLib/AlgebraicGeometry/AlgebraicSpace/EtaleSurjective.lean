module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Property
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Diagonal

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

/-- An fppf sheaf admitting a representable surjective étale map from a scheme has a
representable diagonal. -/
theorem representableDiagonal_of_etaleSurjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf p) :
    yoneda.relativelyRepresentable (Limits.diag F) := sorry

/-- A representable surjective étale map to an fppf sheaf is a representable étale atlas
that is locally surjective for the étale topology. -/
theorem ofEtaleSurjective_isAtlas {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf p) :
    (over (@AlgebraicGeometry.Etale)).presheaf p ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The algebraic space over `S` obtained from an fppf sheaf `F` together with a representable,
surjective, and étale map `p : yoneda.obj U ⟶ F` from a scheme `U` over `S`. -/
def ofEtaleSurjective {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf p) :
    AlgebraicSpace S :=
  ofFunctor F hF (representableDiagonal_of_etaleSurjective hF p hp)
    ⟨U, p, ofEtaleSurjective_isAtlas hF p hp⟩

/-- The functor of points of `ofEtaleSurjective hF p hp` is the given sheaf `F`. -/
@[simp]
theorem ofEtaleSurjective_functorOfPoints {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf p) :
    (ofEtaleSurjective hF p hp).functorOfPoints = F := rfl

/-- The algebraic space `ofEtaleSurjective hF p hp` is an fppf sheaf with representable diagonal
and a representable étale locally-surjective atlas. -/
theorem ofEtaleSurjective_spec {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf p) :
    let X := ofEtaleSurjective hF p hp
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          (over (@AlgebraicGeometry.Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  ⟨hF, representableDiagonal_of_etaleSurjective hF p hp,
    U, p, ofEtaleSurjective_isAtlas hF p hp⟩

/-- The diagonal of the functor of points of `ofEtaleSurjective hF p hp` is representable by
schemes over `S`. -/
theorem ofEtaleSurjective_representableDiagonal {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {U : Over S}
    (p : yoneda.obj U ⟶ F) (hp : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf p) :
    yoneda.relativelyRepresentable (Limits.diag (ofEtaleSurjective hF p hp).functorOfPoints) :=
  (ofEtaleSurjective hF p hp).representableDiagonal

/-- An fppf sheaf admitting a representable surjective étale map from an algebraic space has
a representable diagonal. -/
theorem representableDiagonal_of_etaleSurjectiveSpace {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf a) :
    yoneda.relativelyRepresentable (Limits.diag F) := sorry

/-- An fppf sheaf admitting a representable surjective étale map from an algebraic space has
a representable étale atlas that is locally surjective for the étale topology. -/
theorem exists_etaleAtlas_of_etaleSurjectiveSpace {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf a) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
      (over (@AlgebraicGeometry.Etale)).presheaf p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The algebraic space over `S` obtained from an fppf sheaf `F` together with a representable,
surjective, and étale map `a : G.functorOfPoints ⟶ F` from an algebraic space `G` over `S`. -/
def ofEtaleSurjectiveSpace {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf a) :
    AlgebraicSpace S :=
  ofFunctor F hF (representableDiagonal_of_etaleSurjectiveSpace hF a ha)
    (exists_etaleAtlas_of_etaleSurjectiveSpace hF a ha)

/-- The functor of points of `ofEtaleSurjectiveSpace hF a ha` is the given sheaf `F`. -/
@[simp]
theorem ofEtaleSurjectiveSpace_functorOfPoints {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf a) :
    (ofEtaleSurjectiveSpace hF a ha).functorOfPoints = F := rfl

/-- The algebraic space `ofEtaleSurjectiveSpace hF a ha` is an fppf sheaf with representable
diagonal and a representable étale locally-surjective atlas. -/
theorem ofEtaleSurjectiveSpace_spec {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf a) :
    let X := ofEtaleSurjectiveSpace hF a ha
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          (over (@AlgebraicGeometry.Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  ⟨hF, representableDiagonal_of_etaleSurjectiveSpace hF a ha,
    exists_etaleAtlas_of_etaleSurjectiveSpace hF a ha⟩

/-- The diagonal of the functor of points of `ofEtaleSurjectiveSpace hF a ha` is representable by
schemes over `S`. -/
theorem ofEtaleSurjectiveSpace_representableDiagonal {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf a) :
    yoneda.relativelyRepresentable
      (Limits.diag (ofEtaleSurjectiveSpace hF a ha).functorOfPoints) :=
  (ofEtaleSurjectiveSpace hF a ha).representableDiagonal

/-- The given representable étale-surjective transformation, as a morphism of algebraic spaces. -/
def ofEtaleSurjectiveSpace_hom {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf a) :
    G ⟶ ofEtaleSurjectiveSpace hF a ha :=
  a

/-- The morphism `ofEtaleSurjectiveSpace_hom hF a ha` remains a representable, surjective, and
étale transformation of functors. -/
theorem ofEtaleSurjectiveSpace_hom_etaleSurjective {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf a) :
    (over (@AlgebraicGeometry.Etale ⊓ @AlgebraicGeometry.Surjective)).presheaf (ofEtaleSurjectiveSpace_hom hF a ha) :=
  ha

/-- An fppf sheaf admitting a surjective étale map from an algebraic-space presheaf,
representable by algebraic spaces, is an algebraic space. -/
theorem IsAlgebraicSpace.of_etale_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (ha : relativeAlgebraicSpaces
      (@Surjective S ⊓ @Etale S : MorphismProperty (AlgebraicSpace S)) a) :
    IsAlgebraicSpace F :=
  sorry

/-- An fppf sheaf with diagonal representable by algebraic spaces admitting a
surjective étale map from an algebraic-space presheaf is an algebraic space. -/
theorem IsAlgebraicSpace.of_diag_etale_surjective {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hΔ : representableByAlgebraicSpaces (diag F))
    {X : (Over S)ᵒᵖ ⥤ Type u} [IsAlgebraicSpace X] (a : X ⟶ F)
    (hP : (representableByAlgebraicSpaces.of_diag_isAlgebraicSpace hΔ a).has
      (@Surjective S ⊓ @Etale S : MorphismProperty (AlgebraicSpace S))) :
    IsAlgebraicSpace F :=
  of_etale_surjective hF a
    (relativeAlgebraicSpaces.of _
      (representableByAlgebraicSpaces.of_diag_isAlgebraicSpace hΔ a) hP)

end AlgebraicGeometry.AlgebraicSpace
