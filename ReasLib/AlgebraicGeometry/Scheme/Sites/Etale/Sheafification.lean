module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheafification

variable {S : Scheme.{u}}

/-- Restriction of a presheaf on schemes over `S` to the small étale site of `T`. -/
def restriction (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) : T.left.Etaleᵒᵖ ⥤ Type u :=
  ((Scheme.Etale.forget T.left) ⋙ CategoryTheory.Over.map T.hom).op ⋙ F

/-- The sheafification of the restriction to the small étale site of `T`. -/
noncomputable def localSheaf (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) :
    Sheaf T.left.smallEtaleTopology (Type u) :=
  (presheafToSheaf T.left.smallEtaleTopology (Type u)).obj (restriction F T)

set_option backward.privateInPublic true in
private def pullbackProjection {T T' : Over S} (f : T' ⟶ T) (V : T.left.Etale) :
    ((Scheme.Etale.forget T'.left ⋙ CategoryTheory.Over.map T'.hom).obj
        ((Scheme.smallEtalePullback f.left).obj V)) ⟶
      ((Scheme.Etale.forget T.left ⋙ CategoryTheory.Over.map T.hom).obj V) :=
  CategoryTheory.Over.homMk (pullback.fst V.hom f.left) (by
    change pullback.fst V.hom f.left ≫ (V.hom ≫ T.hom) =
      pullback.snd V.hom f.left ≫ T'.hom
    rw [← Category.assoc, pullback.condition, Category.assoc]
    rw [← CategoryTheory.Over.w f]
    rfl
    )

set_option backward.privateInPublic true in
private def identityPullbackHom {X Y : Scheme} (g : X ⟶ Y) :
    Scheme.Etale.mk (𝟙 X) ⟶ (Scheme.smallEtalePullback g).obj (Scheme.Etale.mk (𝟙 Y)) :=
  CategoryTheory.MorphismProperty.Over.homMk
    (pullback.lift g (𝟙 X) ((Category.comp_id g).trans (Category.id_comp g).symm)) (by
      change pullback.lift g (𝟙 X) _ ≫ pullback.snd (𝟙 Y) g = 𝟙 X
      exact pullback.lift_snd _ _ _)

set_option backward.privateInPublic true in
private def identityOverHom {T : Over S} :
    ((Scheme.Etale.forget T.left ⋙ CategoryTheory.Over.map T.hom).obj
        (Scheme.Etale.mk (𝟙 T.left))) ⟶ T :=
  CategoryTheory.Over.homMk (𝟙 T.left) (by
    change 𝟙 T.left ≫ T.hom = 𝟙 T.left ≫ T.hom
    rfl)

set_option backward.privateInPublic true in
private noncomputable def restrictionComparison {T T' : Over S} (F : (Over S)ᵒᵖ ⥤ Type u)
    (f : T' ⟶ T) :
    restriction F T ⟶
      (Scheme.smallEtalePullback f.left).op ⋙ (localSheaf F T').obj where
  app V := TypeCat.ofHom (fun x ↦
    (toSheafify T'.left.smallEtaleTopology (restriction F T')).app
      (op ((Scheme.smallEtalePullback f.left).obj V.unop))
      (F.map (pullbackProjection f V.unop).op x))
  naturality := by
    intro V W g
    sorry

set_option backward.privateInPublic true in
/-- Restriction of sections along a morphism in the big étale site. -/
noncomputable def restrictionMap {T T' : Over S} (F : (Over S)ᵒᵖ ⥤ Type u)
    (f : T' ⟶ T) :
    (localSheaf F T).obj.obj (op (Scheme.Etale.mk (𝟙 T.left))) ⟶
      (localSheaf F T').obj.obj (op (Scheme.Etale.mk (𝟙 T'.left))) := by
  let h := Functor.op_comp_isSheaf (Scheme.smallEtalePullback f.left)
    T.left.smallEtaleTopology T'.left.smallEtaleTopology (localSheaf F T')
  exact
    (sheafifyLift T.left.smallEtaleTopology (restrictionComparison F f) h).app
        (op (Scheme.Etale.mk (𝟙 T.left))) ≫
      (localSheaf F T').obj.map (identityPullbackHom f.left).op

/-- The étale sheafification of a presheaf on schemes over `S`. -/
noncomputable def sheafify (F : (Over S)ᵒᵖ ⥤ Type u) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := (localSheaf F T.unop).obj.obj (op (Scheme.Etale.mk (𝟙 T.unop.left)))
  map f := restrictionMap F f.unop
  map_id := by
    intro T
    sorry
  map_comp := by
    intro T T' T'' f g
    sorry

/-- Evaluation of étale sheafification at an object is given by its local identity section. -/
theorem sheafify_obj (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) :
    (sheafify F).obj (op T) =
      (localSheaf F T).obj.obj (op (Scheme.Etale.mk (𝟙 T.left))) := by
  rfl

set_option backward.privateInPublic true in
/-- The unit from a presheaf to its étale sheafification. -/
noncomputable def toSheafify (F : (Over S)ᵒᵖ ⥤ Type u) : F ⟶ sheafify F where
  app T :=
    TypeCat.ofHom (fun x ↦
      (CategoryTheory.toSheafify T.unop.left.smallEtaleTopology
        (restriction F T.unop)).app (op (Scheme.Etale.mk (𝟙 T.unop.left)))
        (F.map (identityOverHom (T := T.unop)).op x))
  naturality := by
    intro T T' f
    sorry

/-- Étale descent for the sheafification constructed from local small-site sheafifications. -/
theorem isSheaf (F : (Over S)ᵒᵖ ⥤ Type u) :
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) (sheafify F) := sorry

/-- The universal property of étale sheafification. -/
theorem universal (F : (Over S)ᵒᵖ ⥤ Type u)
    (G : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : F ⟶ G.obj) :
    ∃! θ : sheafify F ⟶ G.obj, toSheafify F ≫ θ = η := by
  sorry

end AlgebraicGeometry.Scheme.EtaleSheafification
