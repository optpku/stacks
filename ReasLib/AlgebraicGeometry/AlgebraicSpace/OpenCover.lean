/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Algebraic spaces from open covers

An fppf sheaf covered by algebraic open subspaces is an algebraic space when the
coproduct of the covering subspaces in fppf sheaves is algebraic.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {I : Type v} {F : (Over S)ᵒᵖ ⥤ Type u}
variable (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
variable {X : I → AlgebraicSpace S} (ι : ∀ i, (X i).functorOfPoints ⟶ F)
variable (h_open : ∀ i, (over (@IsOpenImmersion)).presheaf (ι i))
variable (c : Cofan (fun i ↦
    (⟨(X i).functorOfPoints, (X i).isSheaf⟩ : Sheaf (Scheme.fppfTopology.over S) (Type u))))
variable (hc : IsColimit c)
variable (h_surj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
    (Cofan.IsColimit.desc hc (fun i ↦
      (⟨ι i⟩ : (⟨(X i).functorOfPoints, (X i).isSheaf⟩ :
        Sheaf (Scheme.fppfTopology.over S) (Type u)) ⟶
          (⟨F, hF⟩ : Sheaf (Scheme.fppfTopology.over S) (Type u))))).hom)

include hF ι h_open c hc h_surj

/-- An fppf sheaf covered by representable open immersions from algebraic spaces
has representable diagonal. -/
theorem ofOpenCover_representableDiagonal :
    yoneda.relativelyRepresentable (Limits.diag F) := sorry

variable (h_coprod : IsAlgebraicSpace c.pt.obj)

/-- The atlas of the sheaf coproduct followed by the canonical map to the
covered sheaf. -/
def ofOpenCover_atlasMap : yoneda.obj h_coprod.atlas.choose ⟶ F :=
  h_coprod.atlas.choose_spec.choose ≫
    (Cofan.IsColimit.desc hc (fun i ↦
      (⟨ι i⟩ : (⟨(X i).functorOfPoints, (X i).isSheaf⟩ :
        Sheaf (Scheme.fppfTopology.over S) (Type u)) ⟶
          (⟨F, hF⟩ : Sheaf (Scheme.fppfTopology.over S) (Type u))))).hom

include h_coprod

/-- The composite of the coproduct atlas with the open-cover map is
representable and étale. -/
theorem ofOpenCover_atlasMap_etale :
    presheaf (over (@Etale)) (ofOpenCover_atlasMap hF ι c hc h_coprod) :=
  ⟨Functor.relativelyRepresentable.of_diag
      (ofOpenCover_representableDiagonal hF ι h_open c hc h_surj) _, by
    intro U V g fst snd h
    sorry⟩

/-- The composite of the coproduct atlas with the open-cover map is locally
surjective for the étale topology. -/
theorem ofOpenCover_atlasMap_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      (ofOpenCover_atlasMap hF ι c hc h_coprod) := sorry

/-- An fppf sheaf covered by algebraic open subspaces with algebraic sheaf coproduct
admits a representable étale locally-surjective atlas. -/
theorem ofOpenCover_atlas :
    ∃ (U : Over S) (p : yoneda.obj U ⟶ F),
      presheaf (over (@Etale)) p ∧
        Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  ⟨h_coprod.atlas.choose, ofOpenCover_atlasMap hF ι c hc h_coprod,
    ofOpenCover_atlasMap_etale hF ι h_open c hc h_surj h_coprod,
    ofOpenCover_atlasMap_locallySurjective hF ι h_open c hc h_surj h_coprod⟩

/-- Construct an algebraic space from an fppf sheaf covered by representable open
immersions from algebraic spaces whose sheaf coproduct is algebraic and maps
fppf-locally surjectively to the given sheaf. -/
def ofOpenCover : AlgebraicSpace S :=
  ofFunctor F hF (ofOpenCover_representableDiagonal hF ι h_open c hc h_surj)
    (ofOpenCover_atlas hF ι h_open c hc h_surj h_coprod)

/-- The functor of points of the algebraic space constructed from an open cover
is the original fppf sheaf. -/
@[simp]
theorem ofOpenCover_functorOfPoints :
    (ofOpenCover hF ι h_open c hc h_surj h_coprod).functorOfPoints = F := rfl

/-- The algebraic space constructed from an open cover satisfies fppf descent,
has representable diagonal, and admits a representable étale locally-surjective atlas. -/
theorem ofOpenCover_spec :
    let G := ofOpenCover hF ι h_open c hc h_surj h_coprod
    Presheaf.IsSheaf (Scheme.fppfTopology.over S) G.functorOfPoints ∧
      yoneda.relativelyRepresentable (Limits.diag G.functorOfPoints) ∧
        ∃ (U : Over S) (p : yoneda.obj U ⟶ G.functorOfPoints),
          presheaf (over (@Etale)) p ∧
            Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p :=
  ⟨(ofOpenCover hF ι h_open c hc h_surj h_coprod).isSheaf,
    (ofOpenCover hF ι h_open c hc h_surj h_coprod).representableDiagonal,
    (ofOpenCover hF ι h_open c hc h_surj h_coprod).atlas⟩

/-- Each member of an algebraic open cover maps to the algebraic space constructed
from that cover by its given inclusion. -/
def ofOpenCover_ι (i : I) : X i ⟶ ofOpenCover hF ι h_open c hc h_surj h_coprod :=
  ι i

/-- The morphism from a member of an algebraic open cover has the original
natural transformation as its map on functors of points. -/
theorem ofOpenCover_ι_hom (i : I) :
    ofOpenCover_ι hF ι h_open c hc h_surj h_coprod i = ι i := rfl

/-- The inclusion of each member of an algebraic open cover into the constructed
algebraic space is a representable open immersion. -/
theorem ofOpenCover_ι_presheaf (i : I) :
    (over (@IsOpenImmersion)).presheaf
      (ofOpenCover_ι hF ι h_open c hc h_surj h_coprod i) :=
  h_open i

/-- The inclusion of each member of an algebraic open cover into the constructed
algebraic space is representable by schemes. -/
theorem ofOpenCover_ι_relativelyRepresentable (i : I) :
    yoneda.relativelyRepresentable (ofOpenCover_ι hF ι h_open c hc h_surj h_coprod i) :=
  (h_open i).rep

end AlgebraicGeometry.AlgebraicSpace
