/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Algebraic spaces from étale-surjective maps out of algebraic spaces

An fppf sheaf on `Sch/S` equipped with a representable, surjective, and étale map from an
algebraic space over `S` is itself an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The algebraic space over `S` obtained from an fppf sheaf `F` together with a representable,
surjective, and étale map `a : G.functorOfPoints ⟶ F` from an algebraic space `G` over `S`. -/
def ofEtaleSurjectiveSpace {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@Etale ⊓ @Surjective)).presheaf a) :
    AlgebraicSpace S :=
  ofFunctor F hF sorry sorry

/-- The functor of points of `ofEtaleSurjectiveSpace hF a ha` is the given sheaf `F`. -/
@[simp]
theorem ofEtaleSurjectiveSpace_functorOfPoints {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@Etale ⊓ @Surjective)).presheaf a) :
    (ofEtaleSurjectiveSpace hF a ha).functorOfPoints = F := sorry

/-- The algebraic space `ofEtaleSurjectiveSpace hF a ha` is an fppf sheaf with representable
diagonal and a representable étale locally-surjective atlas. -/
theorem ofEtaleSurjectiveSpace_spec {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@Etale ⊓ @Surjective)).presheaf a) :
    let X := ofEtaleSurjectiveSpace hF a ha
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) X.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag X.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ X.functorOfPoints),
          (over (@Etale)).presheaf p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- The diagonal of the functor of points of `ofEtaleSurjectiveSpace hF a ha` is representable by
schemes over `S`. -/
theorem ofEtaleSurjectiveSpace_representableDiagonal {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@Etale ⊓ @Surjective)).presheaf a) :
    yoneda.relativelyRepresentable
      (Limits.diag (ofEtaleSurjectiveSpace hF a ha).functorOfPoints) := sorry

/-- The given representable étale-surjective transformation, as a morphism of algebraic spaces. -/
def ofEtaleSurjectiveSpace_hom {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@Etale ⊓ @Surjective)).presheaf a) :
    G ⟶ ofEtaleSurjectiveSpace hF a ha :=
  a

/-- The morphism `ofEtaleSurjectiveSpace_hom hF a ha` remains a representable, surjective, and
étale transformation of functors. -/
theorem ofEtaleSurjectiveSpace_hom_etaleSurjective {S : Scheme.{u}} {G : AlgebraicSpace S}
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (a : G.functorOfPoints ⟶ F) (ha : (over (@Etale ⊓ @Surjective)).presheaf a) :
    (over (@Etale ⊓ @Surjective)).presheaf (ofEtaleSurjectiveSpace_hom hF a ha) := sorry

end AlgebraicGeometry.AlgebraicSpace

