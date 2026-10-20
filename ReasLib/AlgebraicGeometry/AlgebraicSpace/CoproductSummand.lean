module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Atlas.Input
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.OpenSubspace.Construction
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Fppf.CoproductSummands

/-!
# Algebraic spaces from sheaf coproduct summands

This module constructs an algebraic space from a sheaf summand of a coproduct
identified with the functor of points of an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits Opposite TopologicalSpace

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The diagonal of a sheaf coproduct summand is representable by schemes over the base scheme. -/
theorem sheafCoprodSummand_representableDiagonal
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    yoneda.relativelyRepresentable (Limits.diag (F i).obj) := sorry

/-- The inclusion `F i ⟶ X` of a sheaf coproduct summand, namely the cofan inclusion followed by
the inverse of the comparison isomorphism `X ≅ ∐ F`. -/
def sheafCoprodSummandInclusion
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    (F i).obj ⟶ X.functorOfPoints :=
  (c.inj i).hom ≫ e.inv

/-- The summand inclusion `F i ⟶ X` is representable (by open and closed immersions), by
Stacks 0F15 applied to the coproduct `∐ F ≅ X`. -/
theorem sheafCoprodSummandInclusion_relativelyRepresentable
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    yoneda.relativelyRepresentable (sheafCoprodSummandInclusion e i) :=
  MorphismProperty.comp_mem _ _ _ (sheafCoprodInj_isOpenAndClosedImmersion hc i).rep
    (Functor.relativelyRepresentable.of_isIso _ e.inv)

/-- The point map induced by all scheme-valued sections of a summand. -/
def sheafCoprodSummandPointMap
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    (Σ U : Over S, (F i).obj.obj (op U) × U.left) → Points X :=
  fun z ↦
    let p : ofOver z.1 ⟶ X :=
      { app := (yonedaEquiv.symm z.2.1 ≫ sheafCoprodSummandInclusion e i).app
        naturality := (yonedaEquiv.symm z.2.1 ≫ sheafCoprodSummandInclusion e i).naturality }
    Points.mapOfOver p z.2.2

/-- The concrete point image of a summand inside the ambient algebraic space. -/
def sheafCoprodSummandPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (e : X.functorOfPoints ≅ c.pt.obj) (i : I) : Set (Points X) :=
  Set.range (sheafCoprodSummandPointMap e i)

/-- The open-and-closed point subset belonging to a coproduct summand. -/
def sheafCoprodSummandPointsOpen
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    TopologicalSpace.Opens (Points X) where
  carrier := sheafCoprodSummandPoints e i
  is_open' := by
    sorry

/-- The open subspace cut out by the summand point image has the summand sheaf as carrier. -/
theorem sheafCoprodSummandOpenSpace_functorOfPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    (OpenSubspace.Construction.space X (sheafCoprodSummandPointsOpen hc e i)).functorOfPoints =
      (F i).obj := by
  sorry

/-- The atlas scheme of a sheaf coproduct summand: the stored atlas of `X` restricted to the
explicit open-and-closed point image of the summand (Stacks 02WP). -/
def sheafCoprodSummandAtlasScheme
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) : Over S :=
  OpenSubspace.Construction.atlas X (sheafCoprodSummandPointsOpen hc e i)

/-- The atlas map of a sheaf coproduct summand: the restricted stored atlas map transported to the
summand sheaf by its carrier identification. -/
def sheafCoprodSummandAtlas
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    yoneda.obj (sheafCoprodSummandAtlasScheme hc e i) ⟶ (F i).obj :=
  OpenSubspace.Construction.atlasMap X (sheafCoprodSummandPointsOpen hc e i) ≫
    eqToHom (sheafCoprodSummandOpenSpace_functorOfPoints hc e i)

/-- The base-changed atlas of a sheaf coproduct summand is representable étale and locally
surjective, being a base change of the étale surjective atlas of `X`. -/
theorem sheafCoprodSummandAtlas_spec
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    MorphismProperty.presheaf (MorphismProperty.over (@Etale)) (sheafCoprodSummandAtlas hc e i) ∧
      Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
        (sheafCoprodSummandAtlas hc e i) := sorry

/-- Construct the algebraic space represented by a sheaf coproduct summand. Its atlas is the stored
atlas of `X` restricted to the explicit summand point image (Stacks 02WP). -/
def ofSheafCoprodSummand
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    AlgebraicSpace S :=
  ofFunctor (F i).obj (F i).property
    (sheafCoprodSummand_representableDiagonal hc e i)
    ⟨sheafCoprodSummandAtlasScheme hc e i, sheafCoprodSummandAtlas hc e i,
      sheafCoprodSummandAtlas_spec hc e i⟩

/-- The functor of points of the constructed summand is its underlying sheaf. -/
@[simp]
theorem ofSheafCoprodSummand_functorOfPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    (ofSheafCoprodSummand hc e i).functorOfPoints = (F i).obj := rfl

/-- The inclusion of the constructed summand into the ambient algebraic space is induced by the
cofan inclusion followed by the inverse of the comparison isomorphism. -/
def ofSheafCoprodSummandι
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    ofSheafCoprodSummand hc e i ⟶ X :=
  sheafCoprodSummandInclusion e i

/-- The underlying natural transformation of the summand inclusion is the cofan inclusion
followed by the inverse comparison isomorphism. -/
theorem ofSheafCoprodSummandι_hom
    {S : Scheme.{u}} {X : AlgebraicSpace S} {I : Type v}
    {F : I → Sheaf (Scheme.fppfTopology.over S) (Type u)}
    {c : Cofan F} (hc : IsColimit c) (e : X.functorOfPoints ≅ c.pt.obj) (i : I) :
    ofSheafCoprodSummandι hc e i = (c.inj i).hom ≫ e.inv := rfl

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
