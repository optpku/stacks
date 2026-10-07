module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Algebraic spaces from sheaf coproduct summands

This module constructs an algebraic space from a sheaf summand of a coproduct
identified with the functor of points of an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The diagonal of a sheaf coproduct summand is representable by schemes over the base scheme. -/
theorem sheafCoprodSummand_representableDiagonal
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    yoneda.relativelyRepresentable (Limits.diag (F i).obj) := sorry

/-- A sheaf coproduct summand admits a representable étale locally-surjective atlas. -/
theorem sheafCoprodSummand_existsAtlas
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ (F i).obj),
      MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

/-- Construct the algebraic space represented by a sheaf coproduct summand. -/
def ofSheafCoprodSummand
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    AlgebraicSpace S :=
  ofFunctor (F i).obj (F i).property
    (sheafCoprodSummand_representableDiagonal hc e i)
    (sheafCoprodSummand_existsAtlas hc e i)

/-- The functor of points of the constructed summand is its underlying sheaf. -/
@[simp]
theorem ofSheafCoprodSummand_functorOfPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    (ofSheafCoprodSummand hc e i).functorOfPoints = (F i).obj := sorry

/-- The inclusion of the constructed summand into the ambient algebraic space is induced by the
cofan inclusion followed by the inverse of the comparison isomorphism. -/
def ofSheafCoprodSummandι
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    ofSheafCoprodSummand hc e i ⟶ X :=
  ((c.inj i).hom ≫ e.inv :
    (ofSheafCoprodSummand hc e i).functorOfPoints ⟶ X.functorOfPoints)

/-- The underlying natural transformation of the summand inclusion is the cofan inclusion
followed by the inverse comparison isomorphism. -/
theorem ofSheafCoprodSummandι_hom
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    ofSheafCoprodSummandι hc e i = (c.inj i).hom ≫ e.inv := sorry

/-- The constructed summand has an fppf sheaf functor of points, representable diagonal, and
representable étale locally-surjective atlas. -/
theorem ofSheafCoprodSummand_spec
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
        (ofSheafCoprodSummand hc e i).functorOfPoints ∧
      yoneda.relativelyRepresentable
        (Limits.diag (ofSheafCoprodSummand hc e i).functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ (ofSheafCoprodSummand hc e i).functorOfPoints),
          MorphismProperty.presheaf (MorphismProperty.over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := sorry

end AlgebraicGeometry.AlgebraicSpace
