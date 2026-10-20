module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import Mathlib.CategoryTheory.Limits.Shapes.Products

/-!
# Fppf locality of algebraic spaces

An fppf sheaf is an algebraic space if its localizations along an fppf covering
and their coproduct in fppf sheaves are algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The fppf sheaf underlying the algebraic-space localization of a presheaf
along a scheme over its base. -/
def fppfLocalizationSheaf {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {I : Type v} (Si : I → Over S)
    (hFi : ∀ i, IsAlgebraicSpace (yoneda.obj (Si i) ⨯ F)) (i : I) :
    Sheaf (Scheme.fppfTopology.over S) (Type u) where
  obj := yoneda.obj (Si i) ⨯ F
  property := (hFi i).isSheaf

/-- The presheaf underlying a localization sheaf is the product of the
representable presheaf with the original presheaf. -/
theorem fppfLocalizationSheaf_obj {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    {I : Type v} (Si : I → Over S)
    (hFi : ∀ i, IsAlgebraicSpace (yoneda.obj (Si i) ⨯ F)) (i : I) :
    (fppfLocalizationSheaf Si hFi i).obj = (yoneda.obj (Si i) ⨯ F) := rfl

/-- An fppf sheaf is an algebraic space if its localizations along an fppf covering
are algebraic spaces and their coproduct in fppf sheaves exists and is an algebraic space. -/
theorem IsAlgebraicSpace.of_fppfLocal {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {I : Type v} (Si : I → Over S) (hSi : Scheme.FppfCovering Si)
    (hFi : ∀ i, IsAlgebraicSpace (yoneda.obj (Si i) ⨯ F))
    [HasCoproduct (fppfLocalizationSheaf Si hFi)]
    (hcoprod : IsAlgebraicSpace (∐ (fppfLocalizationSheaf Si hFi)).obj) :
    IsAlgebraicSpace F :=
  sorry

/-- The canonical first projection from the algebraic space represented by
`yoneda.obj U ⨯ F` to the algebraic space represented by `U`. -/
def yonedaProdFst {S : Scheme.{u}} {U : Over S} {F : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsAlgebraicSpace (yoneda.obj U ⨯ F)) :
    ofFunctor (yoneda.obj U ⨯ F) h.isSheaf h.representableDiagonal h.atlas ⟶ ofOver U :=
  (prod.fst : yoneda.obj U ⨯ F ⟶ yoneda.obj U)

/-- The canonical projection from `yoneda.obj U ⨯ F` is the functor-category
first projection. -/
theorem yonedaProdFst_eq {S : Scheme.{u}} {U : Over S} {F : (Over S)ᵒᵖ ⥤ Type u}
    (h : IsAlgebraicSpace (yoneda.obj U ⨯ F)) :
    yonedaProdFst h = (prod.fst : yoneda.obj U ⨯ F ⟶ yoneda.obj U) := rfl

/-- An fppf sheaf is an algebraic space if its localizations along an fppf
covering are algebraic spaces of finite type over the covering schemes. -/
theorem IsAlgebraicSpace.of_fppfLocal_finiteType {S : Scheme.{u}}
    {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {I : Type v}
    (Si : I → Over S) (hSi : Scheme.FppfCovering Si)
    (hFi : ∀ i, IsAlgebraicSpace (yoneda.obj (Si i) ⨯ F))
    (h_finiteType : ∀ i, FiniteType (yonedaProdFst (hFi i))) :
    IsAlgebraicSpace F :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
