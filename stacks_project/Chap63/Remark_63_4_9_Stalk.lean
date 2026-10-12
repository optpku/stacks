/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import stacks_project.Chap59.Definition_59_29_1_GeometricPoint
public import stacks_project.Chap59.Lemma_59_29_7
public import stacks_project.Chap63.Remark_63_4_9_Pushforward

/-!
# Étale neighbourhood pairing and the stalk formula for `α'`

An étale neighbourhood `(V, v̄)` of `ȳ = g ∘ ȳ'` pulls back to the neighbourhood
`(smallEtalePullback g).obj V` of `ȳ'` with pairing lift `(ȳ', v̄)`. The adjunct
`α'` acts on geometric stalks by this germ formula.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology.Point
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

/-- The geometric point `ȳ = g ∘ ȳ'` of `Y`. -/
noncomputable def imageGeometricPoint {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') : GeometricPoint Y where
  toFieldValuedPoint := FieldValuedPoint.of ybar'.K (ybar'.hom ≫ g)
  isAlgClosed := ybar'.isAlgClosed

/-- The scheme morphism of `imageGeometricPoint g ȳ'` is `ȳ'.hom ≫ g`. -/
theorem imageGeometricPoint_hom {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') :
    (imageGeometricPoint g ybar').hom = ybar'.hom ≫ g :=
  sorry

/-- The étale neighbourhood of `ȳ'` obtained by base change of `(V, v̄)` along `g`,
with pairing lift `(ȳ', v̄)`. -/
noncomputable def pullbackNeighborhood {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (V : GeometricPoint.EtaleNeighborhood (imageGeometricPoint g ybar')) :
    GeometricPoint.EtaleNeighborhood ybar' :=
  GeometricPoint.EtaleNeighborhood.of ((smallEtalePullback g).obj V.toEtale)
    (pullback.lift V.lift ybar'.hom sorry) sorry

/-- The underlying étale object of the pulled-back neighbourhood is the base change of `V`. -/
theorem pullbackNeighborhood_toEtale {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (V : GeometricPoint.EtaleNeighborhood (imageGeometricPoint g ybar')) :
    (pullbackNeighborhood g ybar' V).toEtale = (smallEtalePullback g).obj V.toEtale :=
  sorry

/-- The pairing lift projects to `v̄` on the étale object `V`. -/
theorem pullbackNeighborhood_lift_fst {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (V : GeometricPoint.EtaleNeighborhood (imageGeometricPoint g ybar')) :
    (pullbackNeighborhood g ybar' V).lift ≫ pullback.fst V.toEtale.hom g = V.lift :=
  sorry

/-- The pairing lift projects to `ȳ'` on `Y'`. -/
theorem pullbackNeighborhood_lift_snd {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (V : GeometricPoint.EtaleNeighborhood (imageGeometricPoint g ybar')) :
    (pullbackNeighborhood g ybar' V).lift ≫
      ((smallEtalePullback g).obj V.toEtale).hom = ybar'.hom :=
  sorry

/-- Germ of a section of an abelian étale presheaf at an étale neighbourhood. -/
noncomputable def etaleNeighborhoodGerm {Y : Scheme.{u}} (ybar : GeometricPoint Y)
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
    (V : GeometricPoint.EtaleNeighborhood ybar)
    (G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    G.obj (op V.toEtale) ⟶ (toSmallEtalePoint ybar).presheafFiber.obj G :=
  (toSmallEtalePoint ybar).toPresheafFiber V.toEtale V.2 G

/-- The neighbourhood germ is the site-point map `toPresheafFiber`. -/
theorem etaleNeighborhoodGerm_eq {Y : Scheme.{u}} (ybar : GeometricPoint Y)
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
    (V : GeometricPoint.EtaleNeighborhood ybar)
    (G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) :
    etaleNeighborhoodGerm ybar V G =
      (toSmallEtalePoint ybar).toPresheafFiber V.toEtale V.2 G :=
  sorry

/-- Fibre map sending a lift of `ȳ = g ∘ ȳ'` over `V` to the pairing lift of `ȳ'` over
the base change of `V`. -/
noncomputable def imageToComapFiber {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') :
    (toSmallEtalePoint (imageGeometricPoint g ybar')).fiber ⟶
      smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber where
  app V :=
    TypeCat.ofHom fun (φ : (toSmallEtalePoint (imageGeometricPoint g ybar')).fiber.obj V) ↦
      (Over.homMk (pullback.lift φ.left ybar'.hom sorry) sorry :
        (smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber).obj V)
  naturality := sorry

/-- The pairing lift produced by `imageToComapFiber` projects to the original lift on `V`. -/
theorem imageToComapFiber_fst {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') (V : Y.Etale)
    (φ : (toSmallEtalePoint (imageGeometricPoint g ybar')).fiber.obj V) :
    ((imageToComapFiber g ybar').app V φ).left ≫ pullback.fst V.hom g = φ.left :=
  sorry

/-- The pairing lift produced by `imageToComapFiber` projects to `ȳ'` on `Y'`. -/
theorem imageToComapFiber_snd {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') (V : Y.Etale)
    (φ : (toSmallEtalePoint (imageGeometricPoint g ybar')).fiber.obj V) :
    ((imageToComapFiber g ybar').app V φ).left ≫
      ((smallEtalePullback g).obj V).hom = ybar'.hom :=
  sorry

/-- Fibre map sending a pairing lift of `ȳ'` over the base change of `V` to its projection
to `V`. -/
noncomputable def comapToImageFiber {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') :
    (smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber) ⟶
      (toSmallEtalePoint (imageGeometricPoint g ybar')).fiber where
  app V :=
    TypeCat.ofHom fun (ψ : (smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber).obj V) ↦
      (Over.homMk (ψ.left ≫ pullback.fst V.hom g) sorry :
        (toSmallEtalePoint (imageGeometricPoint g ybar')).fiber.obj V)
  naturality := sorry

/-- The reverse fibre map recovers the original lift by composing with `pullback.fst`. -/
theorem comapToImageFiber_fst {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') (V : Y.Etale)
    (ψ : (smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber).obj V) :
    ((comapToImageFiber g ybar').app V ψ).left = ψ.left ≫ pullback.fst V.hom g :=
  sorry

/-- Identification of the abelian sheaf fibre of `F` at `ȳ = g ∘ ȳ'` with the fibre of
`g⁻¹ F` at `ȳ'`. -/
noncomputable def pullbackSheafFiberIso {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    [InitiallySmall ((smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber).Elements)]
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
    [HasProducts.{u} AddCommGrpCat.{u}]
    [((smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint (imageGeometricPoint g ybar')).sheafFiber.obj F ≅
      (toSmallEtalePoint ybar').sheafFiber.obj
        (((smallEtalePullback g).sheafPullback AddCommGrpCat.{u}
            Y.smallEtaleTopology Y'.smallEtaleTopology).obj F) where
  hom :=
    (Hom.sheafFiber ⟨imageToComapFiber g ybar'⟩).app F ≫
      ((toSmallEtalePoint ybar').sheafFiberComapIsoOfMorphismOfSites (smallEtalePullback g)
          AddCommGrpCat.{u}).hom.app F
  inv :=
    ((toSmallEtalePoint ybar').sheafFiberComapIsoOfMorphismOfSites (smallEtalePullback g)
          AddCommGrpCat.{u}).inv.app F ≫
      (Hom.sheafFiber ⟨comapToImageFiber g ybar'⟩).app F
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `pullbackSheafFiberIso` is the image-to-comap fibre map followed by
the site-point comap comparison. -/
theorem pullbackSheafFiberIso_hom {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    [InitiallySmall ((smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber).Elements)]
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
    [HasProducts.{u} AddCommGrpCat.{u}]
    [((smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (pullbackSheafFiberIso g ybar' F).hom =
      (Hom.sheafFiber ⟨imageToComapFiber g ybar'⟩).app F ≫
        ((toSmallEtalePoint ybar').sheafFiberComapIsoOfMorphismOfSites (smallEtalePullback g)
            AddCommGrpCat.{u}).hom.app F :=
  sorry

/-- On geometric stalks, `α'` sends the germ of a section `s` of `G` over an étale
neighbourhood `(V, v̄)` of `ȳ = g ∘ ȳ'` to the germ of `α(s)` over the pulled-back
neighbourhood of `ȳ'`. -/
theorem sheafifyPresheafPushforwardAdjoint_stalk {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    [HasWeakSheafify Y.smallEtaleTopology AddCommGrpCat.{u}]
    [HasWeakSheafify Y'.smallEtaleTopology AddCommGrpCat.{u}]
    [((smallEtalePullback g).sheafPushforwardContinuous AddCommGrpCat.{u}
        Y.smallEtaleTopology Y'.smallEtaleTopology).IsRightAdjoint]
    [InitiallySmall ((smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber).Elements)]
    [HasColimitsOfSize.{u, u} AddCommGrpCat.{u}]
    [HasProducts.{u} AddCommGrpCat.{u}]
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G')
    (V : GeometricPoint.EtaleNeighborhood (imageGeometricPoint g ybar')) :
    etaleNeighborhoodGerm (imageGeometricPoint g ybar') V G ≫
        ((toSmallEtalePoint (imageGeometricPoint g ybar')).presheafToSheafCompSheafFiberIso
            AddCommGrpCat.{u}).inv.app G ≫
          (pullbackSheafFiberIso g ybar'
              ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G)).hom ≫
            (toSmallEtalePoint ybar').sheafFiber.map
              (sheafifyPresheafPushforwardAdjoint g α) =
      α.app (op V.toEtale) ≫
        etaleNeighborhoodGerm ybar' (pullbackNeighborhood g ybar' V) G' ≫
          ((toSmallEtalePoint ybar').presheafToSheafCompSheafFiberIso
              AddCommGrpCat.{u}).inv.app G' :=
  sorry

end AlgebraicGeometry.Scheme.Etale
