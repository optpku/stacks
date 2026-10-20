module

public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.Point.Category
public import Mathlib.CategoryTheory.Sites.Point.Skyscraper
public import ReasLib.CategoryTheory.Sites.Point.MorphismOfSites
public import ReasLib.AlgebraicGeometry.Scheme.GeometricPoint.Map
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.InverseImageStalk
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PresheafPushforward

/-!
# Pullback of étale neighborhoods and abelian stalks

Base change pairs a pointed étale neighborhood of an image geometric point with the
original geometric point. The resulting comparison of abelian stalks computes the
inverse-image adjunct of a sheafified presheaf morphism on canonical germs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.GrothendieckTopology.Point
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint
open AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The category of lifts from a field-valued point to pulled-back étale objects is initially
small. -/
instance smallEtalePullback_fiberElements_initiallySmall {Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (K : Type u) [Field K] (point : Spec (.of K) ⟶ Y') :
    InitiallySmall.{u} ((smallEtalePullback g ⋙
      (Etale.forget Y' ⋙ coyoneda.obj (op (Over.mk point)))).Elements) :=
  smallEtalePullback_fiber_initiallySmall g K point

/-- The pairing lift produced by `smallEtaleInverseImage_comapFiberInv` projects to the original lift on `V`. -/
theorem smallEtaleInverseImage_comapFiberInv_fst {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') (V : Y.Etale)
    (φ : (toSmallEtalePoint (ybar'.map g)).fiber.obj V) :
    ((smallEtaleInverseImage_comapFiberInv g ybar').app V φ).left ≫ pullback.fst V.hom g = φ.left :=
  sorry

/-- The pairing lift produced by `smallEtaleInverseImage_comapFiberInv` projects to `ȳ'` on `Y'`. -/
theorem smallEtaleInverseImage_comapFiberInv_snd {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') (V : Y.Etale)
    (φ : (toSmallEtalePoint (ybar'.map g)).fiber.obj V) :
    ((smallEtaleInverseImage_comapFiberInv g ybar').app V φ).left ≫
      ((smallEtalePullback g).obj V).hom = ybar'.hom :=
  sorry

/-- The reverse fibre map recovers the original lift by composing with `pullback.fst`. -/
theorem smallEtaleInverseImage_comapFiberHom_fst {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y') (V : Y.Etale)
    (ψ : (smallEtalePullback g ⋙ (toSmallEtalePoint ybar').fiber).obj V) :
    ((smallEtaleInverseImage_comapFiberHom g ybar').app V ψ).left = ψ.left ≫ pullback.fst V.hom g :=
  sorry

/-- Projection followed by pairing is the identity on the pulled-back fiber functor. -/
theorem smallEtaleInverseImage_comapFiber_hom_inv_id {Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (ybar' : GeometricPoint Y') :
    smallEtaleInverseImage_comapFiberHom g ybar' ≫
      smallEtaleInverseImage_comapFiberInv g ybar' = 𝟙 _ :=
  sorry

/-- Pairing followed by projection is the identity on the image-point fiber functor. -/
theorem smallEtaleInverseImage_comapFiber_inv_hom_id {Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (ybar' : GeometricPoint Y') :
    smallEtaleInverseImage_comapFiberInv g ybar' ≫
      smallEtaleInverseImage_comapFiberHom g ybar' = 𝟙 _ :=
  sorry

namespace Etale

/-- The étale neighbourhood of `ȳ'` obtained by base change of `(V, v̄)` along `g`,
with pairing lift `(ȳ', v̄)`. -/
noncomputable def pullbackNeighborhood {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (V : GeometricPoint.EtaleNeighborhood (ybar'.map g)) :
    GeometricPoint.EtaleNeighborhood ybar' :=
  Functor.elementsMk _ ((smallEtalePullback g).obj V.toEtale)
    ((smallEtaleInverseImage_comapFiberInv g ybar').app V.toEtale V.2)

/-- The underlying étale object of the pulled-back neighbourhood is the base change of `V`. -/
theorem pullbackNeighborhood_toEtale {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (V : GeometricPoint.EtaleNeighborhood (ybar'.map g)) :
    (pullbackNeighborhood g ybar' V).toEtale = (smallEtalePullback g).obj V.toEtale :=
  sorry

/-- The pairing lift projects to `v̄` on the étale object `V`. -/
theorem pullbackNeighborhood_lift_fst {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (V : GeometricPoint.EtaleNeighborhood (ybar'.map g)) :
    (pullbackNeighborhood g ybar' V).lift ≫ pullback.fst V.toEtale.hom g = V.lift :=
  sorry

/-- The pairing lift projects to `ȳ'` on `Y'`. -/
theorem pullbackNeighborhood_lift_snd {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (V : GeometricPoint.EtaleNeighborhood (ybar'.map g)) :
    (pullbackNeighborhood g ybar' V).lift ≫
      ((smallEtalePullback g).obj V.toEtale).hom = ybar'.hom :=
  sorry

/-- Identification of the abelian sheaf fibre of `F` at `ȳ = g ∘ ȳ'` with the fibre of
`g⁻¹ F` at `ȳ'`. -/
noncomputable def pullbackSheafFiberIso {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (toSmallEtalePoint (ybar'.map g)).sheafFiber.obj F ≅
      (toSmallEtalePoint ybar').sheafFiber.obj
        (((smallEtalePullback g).sheafPullback AddCommGrpCat.{u}
            Y.smallEtaleTopology Y'.smallEtaleTopology).obj F) :=
  let p := (toSmallEtalePoint ybar').comapOfMorphismOfSites
    (h_small := smallEtalePullback_fiberElements_initiallySmall g ybar'.K ybar'.hom)
    (smallEtalePullback g)
  let i : (toSmallEtalePoint (ybar'.map g)).sheafFiber.obj F ≅ p.sheafFiber.obj F :=
    { hom := (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberInv g ybar'⟩).app F
      inv := (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberHom g ybar'⟩).app F
      hom_inv_id := by
        have h : (⟨smallEtaleInverseImage_comapFiberInv g ybar' ≫
            smallEtaleInverseImage_comapFiberHom g ybar'⟩ :
            toSmallEtalePoint (ybar'.map g) ⟶ toSmallEtalePoint (ybar'.map g)) =
            𝟙 (toSmallEtalePoint (ybar'.map g)) := by
          apply hom_ext
          exact smallEtaleInverseImage_comapFiber_inv_hom_id g ybar'
        change ((Hom.sheafFiber (A := AddCommGrpCat.{u})
          ⟨smallEtaleInverseImage_comapFiberInv g ybar'⟩) ≫
          (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberHom g ybar'⟩)).app F = _
        rw [← Hom.sheafFiber_comp]
        exact (congrArg
          (fun (t : toSmallEtalePoint (ybar'.map g) ⟶ toSmallEtalePoint (ybar'.map g)) =>
            (Hom.sheafFiber (A := AddCommGrpCat.{u}) t).app F) h).trans
          (NatTrans.congr_app
            (Hom.sheafFiber_id (A := AddCommGrpCat.{u}) (toSmallEtalePoint (ybar'.map g))) F)
      inv_hom_id := by
        have h : (⟨smallEtaleInverseImage_comapFiberHom g ybar' ≫
            smallEtaleInverseImage_comapFiberInv g ybar'⟩ : p ⟶ p) = 𝟙 p := by
          apply hom_ext
          exact smallEtaleInverseImage_comapFiber_hom_inv_id g ybar'
        change ((Hom.sheafFiber (A := AddCommGrpCat.{u})
          ⟨smallEtaleInverseImage_comapFiberHom g ybar'⟩) ≫
          (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberInv g ybar'⟩)).app F = _
        rw [← Hom.sheafFiber_comp]
        exact (congrArg (fun (t : p ⟶ p) =>
          (Hom.sheafFiber (A := AddCommGrpCat.{u}) t).app F) h).trans
          (NatTrans.congr_app (Hom.sheafFiber_id (A := AddCommGrpCat.{u}) p) F) }
  i ≪≫ ((toSmallEtalePoint ybar').sheafFiberComapIsoOfMorphismOfSites
    (h_small := smallEtalePullback_fiberElements_initiallySmall g ybar'.K ybar'.hom)
    (smallEtalePullback g) AddCommGrpCat.{u}).app F

/-- The forward map of `pullbackSheafFiberIso` is the image-to-comap fibre map followed by
the site-point comap comparison. -/
theorem pullbackSheafFiberIso_hom {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u}) :
    (pullbackSheafFiberIso g ybar' F).hom =
      (Hom.sheafFiber ⟨smallEtaleInverseImage_comapFiberInv g ybar'⟩).app F ≫
        ((toSmallEtalePoint ybar').sheafFiberComapIsoOfMorphismOfSites
          (h_small := smallEtalePullback_fiberElements_initiallySmall g ybar'.K ybar'.hom)
          (smallEtalePullback g)
            AddCommGrpCat.{u}).hom.app F :=
  sorry

/-- On geometric stalks, `α'` sends the germ of a section `s` of `G` over an étale
neighbourhood `(V, v̄)` of `ȳ = g ∘ ȳ'` to the germ of `α(s)` over the pulled-back
neighbourhood of `ȳ'`. -/
theorem sheafifyPresheafPushforwardAdjoint_stalk {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G')
    (V : GeometricPoint.EtaleNeighborhood (ybar'.map g)) :
    (toSmallEtalePoint (ybar'.map g)).toPresheafFiber V.toEtale V.2 G ≫
        ((toSmallEtalePoint (ybar'.map g)).presheafToSheafCompSheafFiberIso
            AddCommGrpCat.{u}).inv.app G ≫
          (pullbackSheafFiberIso g ybar'
              ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G)).hom ≫
            (toSmallEtalePoint ybar').sheafFiber.map
              (sheafifyPresheafPushforwardAdjoint g α) =
      α.app (op V.toEtale) ≫
        (toSmallEtalePoint ybar').toPresheafFiber
          (pullbackNeighborhood g ybar' V).toEtale (pullbackNeighborhood g ybar' V).2 G' ≫
          ((toSmallEtalePoint ybar').presheafToSheafCompSheafFiberIso
              AddCommGrpCat.{u}).inv.app G' :=
  sorry

end Etale

end AlgebraicGeometry.Scheme
