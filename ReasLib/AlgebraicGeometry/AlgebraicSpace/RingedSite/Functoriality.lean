module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.InverseImage
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.Pullback
public import ReasLib.AlgebraicGeometry.RingedSite.Topos.TwoMorphism.Arbitrary

/-!
# Functoriality of small étale ringed topoi of algebraic spaces

The canonical morphism of small étale ringed topoi respects composition and identities.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AlgebraicSpace

namespace EtaleTopos

/-- Direct image along successive morphisms of algebraic spaces is canonically isomorphic
to direct image along their composite. -/
def directImageCompIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y ⟶ Z) : directImage f ⋙ directImage g ≅ directImage (f ≫ g) := by
  let P := (spacesEtalePullback f).sheafPushforwardContinuous (Type u)
    (spacesEtaleTopology Y) (spacesEtaleTopology X)
  let chartIso (U : smallEtaleSite Y) :
      (etaleBaseChange f).obj U ≅ (spacesEtalePullback f).obj
        ((smallEtaleToSpaces Y).obj U) :=
    { hom := MorphismProperty.Over.homMk
        (pullback.lift (f := U.hom) (g := f)
          (etaleBaseChangeSnd f U) (etaleBaseChangeHom f U) (by sorry)) (by sorry)
      inv := MorphismProperty.Over.homMk
        (pullback.lift (f := homFunctor f) (g := homFunctor U.hom)
          (homFunctor (pullback.snd U.hom f))
          (homFunctor (pullback.fst U.hom f)) (by sorry)) (by sorry)
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  let compositeIso (V : smallEtaleSite Z) :
      (etaleBaseChange (f ≫ g)).obj V ≅
        (spacesEtalePullback f).obj ((etaleBaseChange g).obj V) :=
    { hom := MorphismProperty.Over.homMk
        (pullback.lift (f := ((etaleBaseChange g).obj V).hom) (g := f)
          (pullback.lift (f := homFunctor g) (g := homFunctor V.hom)
            (etaleBaseChangeFst (f ≫ g) V ≫ homFunctor f)
            (etaleBaseChangeSnd (f ≫ g) V) (by sorry))
          (etaleBaseChangeHom (f ≫ g) V) (by sorry)) (by sorry)
      inv := MorphismProperty.Over.homMk
        (pullback.lift (f := homFunctor (f ≫ g)) (g := homFunctor V.hom)
          (homFunctor (pullback.snd ((etaleBaseChange g).obj V).hom f))
          (homFunctor (pullback.fst ((etaleBaseChange g).obj V).hom f) ≫
            etaleBaseChangeSnd g V) (by sorry)) (by sorry)
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  refine NatIso.ofComponents (fun Q ↦ ?_) ?_
  swap
  · sorry
  let N := (extension X).obj Q
  let e : (directImage f).obj Q ≅ (restriction Y).obj (P.obj N) :=
    { hom := ⟨{ app := fun U ↦ N.obj.map (chartIso U.unop).inv.op,
                naturality := by sorry }⟩
      inv := ⟨{ app := fun U ↦ N.obj.map (chartIso U.unop).hom.op,
                naturality := by sorry }⟩
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  let extended := (extension Y).mapIso e ≪≫
    (restrictionExtensionIso Y).symm.app (P.obj N)
  exact
    { hom := ⟨{ app := fun V ↦
                  extended.hom.hom.app (op ((etaleBaseChange g).obj V.unop)) ≫
                    N.obj.map (compositeIso V.unop).hom.op,
                naturality := by sorry }⟩
      inv := ⟨{ app := fun V ↦ N.obj.map (compositeIso V.unop).inv.op ≫
                  extended.inv.hom.app (op ((etaleBaseChange g).obj V.unop)),
                naturality := by sorry }⟩
      hom_inv_id := by sorry
      inv_hom_id := by sorry }

/-- Direct image along the identity of an algebraic space is canonically isomorphic
to the identity functor on its small étale sheaves. -/
def directImageIdIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    directImage (𝟙 X) ≅ 𝟭 (Sheaf (smallEtaleTopology X) (Type u)) := by
  let chartIso (U : smallEtaleSite X) :
      (etaleBaseChange (𝟙 X)).obj U ≅ (smallEtaleToSpaces X).obj U :=
    { hom := MorphismProperty.Over.homMk (etaleBaseChangeSnd (𝟙 X) U) (by sorry)
      inv := MorphismProperty.Over.homMk
        (pullback.lift (f := homFunctor (𝟙 X)) (g := homFunctor U.hom)
          U.hom (𝟙 _) (by sorry)) (by sorry)
      hom_inv_id := by sorry
      inv_hom_id := by sorry }
  refine NatIso.ofComponents (fun Q ↦ ?_) ?_
  swap
  · sorry
  let N := (extension X).obj Q
  exact
    { hom := ⟨{ app := fun U ↦ N.obj.map (chartIso U.unop).inv.op ≫
                  ((extensionRestrictionIso X).hom.app Q).hom.app U,
                naturality := by sorry }⟩
      inv := ⟨{ app := fun U ↦ ((extensionRestrictionIso X).inv.app Q).hom.app U ≫
                  N.obj.map (chartIso U.unop).hom.op,
                naturality := by sorry }⟩
      hom_inv_id := by sorry
      inv_hom_id := by sorry }

end EtaleTopos

/-- The canonical ringed-topos morphism of a composite is canonically isomorphic
to the composite of the canonical ringed-topos morphisms. -/
def ringedToposHomCompIso {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y)
    (g : Y ⟶ Z) :
    RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u}
      (RingedSite.ToposHom.comp.{u + 1, u, u + 1, u, u + 1, u, u} (ringedToposHom f) (ringedToposHom g))
      (ringedToposHom (f ≫ g)) where
  homIso := EtaleTopos.directImageCompIso f g
  comm := by sorry

/-- The canonical ringed-topos morphism associated to an identity is canonically
isomorphic to the identity ringed-topos morphism. -/
def ringedToposHomIdIso {S : Scheme.{u}} (X : AlgebraicSpace S) :
    RingedSite.ToposHom.TwoIso.{u + 1, u, u + 1, u, u} (ringedToposHom (𝟙 X))
      (RingedSite.ToposHom.id (ringedSite X)) where
  homIso := EtaleTopos.directImageIdIso X
  comm := by sorry

end AlgebraicGeometry.AlgebraicSpace
