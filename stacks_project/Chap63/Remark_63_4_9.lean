module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.PresheafPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Stalk.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite
open CategoryTheory.GrothendieckTopology.Point
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.GeometricPoint AlgebraicGeometry.Scheme.Etale

noncomputable section

universe u

#check (AlgebraicGeometry.Scheme.Etale.presheafPushforwardAb :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y),
    (Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ (Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}))

#check (AlgebraicGeometry.Scheme.Etale.presheafPushforwardAb_app :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}) (V : Y.Etale),
    ((presheafPushforwardAb g).obj G').obj (op V) =
      G'.obj (op ((smallEtalePullback g).obj V)))

#check (AlgebraicGeometry.Scheme.Etale.sheafifyPresheafPushforward :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G'),
    (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G ⟶
      (smallEtalePushforwardAb g).obj
        ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G'))

#check (AlgebraicGeometry.Scheme.Etale.sheafifyPresheafPushforward_commSq :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G'),
    CommSq α (toSheafify Y.smallEtaleTopology G)
      (whiskerLeft (smallEtalePullback g).op (toSheafify Y'.smallEtaleTopology G'))
      (sheafifyPresheafPushforward g α).hom)

#check (AlgebraicGeometry.Scheme.Etale.sheafifyPresheafPushforward_unique :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G')
    (β : (presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G ⟶
      (smallEtalePushforwardAb g).obj
        ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G'))
    (hβ : CommSq α (toSheafify Y.smallEtaleTopology G)
      (whiskerLeft (smallEtalePullback g).op (toSheafify Y'.smallEtaleTopology G')) β.hom),
    β = sheafifyPresheafPushforward g α)

#check (AlgebraicGeometry.Scheme.Etale.sheafifyPresheafPushforwardAdjoint :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G'),
    ((smallEtalePullback g).sheafPullback AddCommGrpCat.{u}
          Y.smallEtaleTopology Y'.smallEtaleTopology).obj
        ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G) ⟶
      (presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G')

#check (AlgebraicGeometry.Scheme.Etale.sheafifyPresheafPushforwardAdjoint_homEquiv :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G'),
    ((smallEtalePullback g).sheafAdjunctionContinuous AddCommGrpCat.{u}
          Y.smallEtaleTopology Y'.smallEtaleTopology).homEquiv
        ((presheafToSheaf Y.smallEtaleTopology AddCommGrpCat.{u}).obj G)
        ((presheafToSheaf Y'.smallEtaleTopology AddCommGrpCat.{u}).obj G')
        (sheafifyPresheafPushforwardAdjoint g α) =
      sheafifyPresheafPushforward g α)

/- Remark 63.4.9: the adjunct of the unique sheafification lift sends a germ over a
pointed étale neighborhood of the image geometric point to the germ of its image under
α over the pulled-back pointed neighborhood. -/
@[stacks 0F78]
#check (AlgebraicGeometry.Scheme.Etale.sheafifyPresheafPushforwardAdjoint_stalk :
    ∀ {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    (ybar' : GeometricPoint Y')
    {G : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}} {G' : Y'.Etaleᵒᵖ ⥤ AddCommGrpCat.{u}}
    (α : G ⟶ (presheafPushforwardAb g).obj G')
    (V : GeometricPoint.EtaleNeighborhood (ybar'.map g)),
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
              AddCommGrpCat.{u}).inv.app G')

end
