module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Algebraic spaces from open covers by algebraic spaces

A sheaf on `(Sch/S)_fppf` that is covered by a not-too-large family of algebraic-space
open subfunctors is itself an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

/-- The morphism of functors of points `∐ X i ⟶ F` induced by a family of maps from algebraic
spaces into a presheaf `F`. -/
def openCoverDesc {S : Scheme.{u}} {I : Type v} [Small.{u} I] {F : (Over S)ᵒᵖ ⥤ Type u}
    (X : I → AlgebraicSpace S) (ι : ∀ i, (X i).functorOfPoints ⟶ F) :
    (∐ fun i ↦ (X i).functorOfPoints) ⟶ F :=
  Sigma.desc fun i ↦ ι i

/-- Postcomposing the `i`-th coproduct inclusion with `openCoverDesc X ι` recovers `ι i`. -/
theorem openCoverDesc_ι {S : Scheme.{u}} {I : Type v} [Small.{u} I] {F : (Over S)ᵒᵖ ⥤ Type u}
    (X : I → AlgebraicSpace S) (ι : ∀ i, (X i).functorOfPoints ⟶ F) (i : I) :
    Sigma.ι (fun j ↦ (X j).functorOfPoints) i ≫ openCoverDesc X ι = ι i :=
  sorry

/-- The algebraic space over `S` obtained from an fppf sheaf `F` covered by a not-too-large family
of algebraic spaces `X i` whose inclusions `ι i` are representable open immersions in the sense of
`MorphismProperty.presheaf` / Definition 65.5.1, and whose coproduct map `openCoverDesc X ι` is
surjective as a map of sheaves. The size hypothesis that `∐ X i` is an algebraic space is encoded
by `[Small.{u} I]`, as in Lemma 65.8.4. The subspace reading `X i ⊂ F` is the monomorphism implied
by an open immersion, not a `Subfunctor` parameter. The functor of points is the given sheaf `F`. -/
def ofOpenCover {S : Scheme.{u}} {I : Type v} [Small.{u} I] {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {X : I → AlgebraicSpace S}
    (ι : ∀ i, (X i).functorOfPoints ⟶ F)
    (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (openCoverDesc X ι)) :
    AlgebraicSpace S :=
  ofFunctor F hF sorry sorry

/-- The functor of points of `ofOpenCover hF ι h_open h_surj` is the given sheaf `F`. -/
@[simp]
theorem ofOpenCover_functorOfPoints {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : I → AlgebraicSpace S} (ι : ∀ i, (X i).functorOfPoints ⟶ F)
    (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (openCoverDesc X ι)) :
    (ofOpenCover hF ι h_open h_surj).functorOfPoints = F :=
  sorry

/-- The algebraic space `ofOpenCover hF ι h_open h_surj` is an fppf sheaf with representable
diagonal and a representable étale locally-surjective atlas. -/
theorem ofOpenCover_spec {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : I → AlgebraicSpace S} (ι : ∀ i, (X i).functorOfPoints ⟶ F)
    (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (openCoverDesc X ι)) :
    let G := ofOpenCover hF ι h_open h_surj
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) G.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag G.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ G.functorOfPoints),
          presheaf (over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  sorry

/-- The given inclusion of the `i`-th algebraic space, as a morphism of algebraic spaces into
`ofOpenCover hF ι h_open h_surj`. -/
def ofOpenCover_ι {S : Scheme.{u}} {I : Type v} [Small.{u} I] {F : (Over S)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F) {X : I → AlgebraicSpace S}
    (ι : ∀ i, (X i).functorOfPoints ⟶ F)
    (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (openCoverDesc X ι))
    (i : I) : X i ⟶ ofOpenCover hF ι h_open h_surj :=
  ι i

/-- The morphism `ofOpenCover_ι hF ι h_open h_surj i` is the given inclusion `ι i`. -/
theorem ofOpenCover_ι_hom {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : I → AlgebraicSpace S} (ι : ∀ i, (X i).functorOfPoints ⟶ F)
    (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (openCoverDesc X ι))
    (i : I) : ofOpenCover_ι hF ι h_open h_surj i = ι i :=
  sorry

/-- The inclusion `ofOpenCover_ι hF ι h_open h_surj i` is a representable open immersion in the
sense of Definition 65.5.1. -/
theorem ofOpenCover_ι_presheaf {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : I → AlgebraicSpace S} (ι : ∀ i, (X i).functorOfPoints ⟶ F)
    (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (openCoverDesc X ι))
    (i : I) : (over (@IsOpenImmersion)).presheaf (ofOpenCover_ι hF ι h_open h_surj i) :=
  sorry

/-- The inclusion `ofOpenCover_ι hF ι h_open h_surj i` is representable as a transformation of
functors of points. -/
theorem ofOpenCover_ι_relativelyRepresentable {S : Scheme.{u}} {I : Type v} [Small.{u} I]
    {F : (Over S)ᵒᵖ ⥤ Type u} (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    {X : I → AlgebraicSpace S} (ι : ∀ i, (X i).functorOfPoints ⟶ F)
    (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
    (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (openCoverDesc X ι))
    (i : I) : yoneda.relativelyRepresentable (ofOpenCover_ι hF ι h_open h_surj i) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
