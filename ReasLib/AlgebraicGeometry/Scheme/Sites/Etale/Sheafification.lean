/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.Sheafification
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Pullback
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.EtaleSheafification

variable {S : Scheme.{u}}

/-- The functor sending an étale scheme over a test scheme to its object over the base. -/
def testFunctor (T : Over S) : T.left.Etale ⥤ Over S :=
  Scheme.Etale.forget T.left ⋙ Over.map T.hom

/-- Restriction of a presheaf on schemes over `S` to the small étale site of `T`. -/
def restriction (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) : T.left.Etaleᵒᵖ ⥤ Type u :=
  ((Scheme.Etale.forget T.left) ⋙ CategoryTheory.Over.map T.hom).op ⋙ F

/-- The sheafification of the restriction to the small étale site of `T`. -/
noncomputable def localSheaf (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) :
    Sheaf T.left.smallEtaleTopology (Type u) :=
  (presheafToSheaf T.left.smallEtaleTopology (Type u)).obj (restriction F T)

set_option backward.isDefEq.respectTransparency false in
/-- The base-change projections form a natural transformation of test schemes. -/
def testProjection {X Y : Over S} (g : X ⟶ Y) :
    Scheme.smallEtalePullback g.left ⋙ testFunctor X ⟶ testFunctor Y where
  app E := Over.homMk (pullback.fst E.hom g.left) (by
    change pullback.fst E.hom g.left ≫ (E.hom ≫ Y.hom) =
      pullback.snd E.hom g.left ≫ X.hom
    rw [← Category.assoc, pullback.condition, Category.assoc, Over.w g])
  naturality E F h := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _

/-- Presheaf restriction is induced by the pullback projections. -/
def presheafRestrictionMap (P : (Over S)ᵒᵖ ⥤ Type u) {X Y : Over S} (g : X ⟶ Y) :
    restriction P Y ⟶ (Scheme.smallEtalePullback g.left).op ⋙ restriction P X :=
  Functor.whiskerRight (NatTrans.op (testProjection g)) P

set_option backward.privateInPublic true in
private def identityPullbackHom {X Y : Scheme} (g : X ⟶ Y) :
    Scheme.Etale.mk (𝟙 X) ⟶ (Scheme.smallEtalePullback g).obj (Scheme.Etale.mk (𝟙 Y)) :=
  CategoryTheory.MorphismProperty.Over.homMk
    (pullback.lift g (𝟙 X) ((Category.comp_id g).trans (Category.id_comp g).symm)) (by
      change pullback.lift g (𝟙 X) _ ≫ pullback.snd (𝟙 Y) g = 𝟙 X
      exact pullback.lift_snd _ _ _)

set_option backward.privateInPublic true in
private def identityOverHom {T : Over S} :
    (testFunctor T).obj (Scheme.Etale.mk (𝟙 T.left)) ⟶ T :=
  CategoryTheory.Over.homMk (𝟙 T.left) (by
    change 𝟙 T.left ≫ T.hom = 𝟙 T.left ≫ T.hom
    rfl)

set_option backward.privateInPublic true in
private noncomputable def restrictionComparison {T T' : Over S} (F : (Over S)ᵒᵖ ⥤ Type u)
    (f : T' ⟶ T) :
    restriction F T ⟶
      (Scheme.smallEtalePullback f.left).op ⋙ (localSheaf F T').obj :=
  presheafRestrictionMap F f ≫ Functor.whiskerLeft (Scheme.smallEtalePullback f.left).op
    (CategoryTheory.toSheafify T'.left.smallEtaleTopology (restriction F T'))

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

/-- Restricting a local identity section along the identity is the identity. -/
theorem restrictionMap_id (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) :
    restrictionMap F (𝟙 T) = 𝟙 _ := sorry

/-- Restricting local identity sections respects composition of test morphisms. -/
theorem restrictionMap_comp (F : (Over S)ᵒᵖ ⥤ Type u)
    {T T' T'' : Over S} (f : T' ⟶ T) (g : T'' ⟶ T') :
    restrictionMap F (g ≫ f) = restrictionMap F f ≫ restrictionMap F g := sorry

/-- The étale sheafification of a presheaf on schemes over `S`. -/
noncomputable def sheafify (F : (Over S)ᵒᵖ ⥤ Type u) : (Over S)ᵒᵖ ⥤ Type u where
  obj T := (localSheaf F T.unop).obj.obj (op (Scheme.Etale.mk (𝟙 T.unop.left)))
  map f := restrictionMap F f.unop
  map_id T := restrictionMap_id F T.unop
  map_comp := by
    intro X Y Z f g
    exact restrictionMap_comp F f.unop g.unop

/-- Evaluation of étale sheafification at an object is given by its local identity section. -/
theorem sheafify_obj (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) :
    (sheafify F).obj (op T) =
      (localSheaf F T).obj.obj (op (Scheme.Etale.mk (𝟙 T.left))) := by
  rfl

set_option backward.privateInPublic true in
/-- The unit section at the identity object of the local étale site. -/
def unitSection (F : (Over S)ᵒᵖ ⥤ Type u) (T : Over S) :
    F.obj (op T) → (localSheaf F T).obj.obj (op (Scheme.Etale.mk (𝟙 T.left))) :=
  fun x ↦ (CategoryTheory.toSheafify T.left.smallEtaleTopology
    (restriction F T)).app (op (Scheme.Etale.mk (𝟙 T.left)))
      (F.map (identityOverHom (T := T)).op x)

/-- The local unit sections commute with restriction of test schemes. -/
theorem unitSection_naturality (F : (Over S)ᵒᵖ ⥤ Type u)
    {T T' : Over S} (f : T' ⟶ T) :
    F.map f.op ≫ TypeCat.ofHom (unitSection F T') =
      TypeCat.ofHom (unitSection F T) ≫ restrictionMap F f := sorry

/-- The unit from a presheaf to its étale sheafification. -/
noncomputable def toSheafify (F : (Over S)ᵒᵖ ⥤ Type u) : F ⟶ sheafify F where
  app T := TypeCat.ofHom (unitSection F T.unop)
  naturality := by
    intro X Y f
    exact unitSection_naturality F f.unop

/-- Étale descent for the sheafification constructed from local small-site sheafifications. -/
theorem isSheaf (F : (Over S)ᵒᵖ ⥤ Type u) :
    Presheaf.IsSheaf (Scheme.etaleTopology.over S) (sheafify F) := sorry

/-- The étale-site inclusion is continuous for its actual induced topology. -/
instance forget_continuous (T : Scheme.{u}) :
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T).IsContinuous
      T.smallEtaleTopology (Scheme.etaleTopology.over T) := by
  -- Local instance justification (proof-local temporary data): use finite-limit creation to prove this forgetful functor flat.
  letI : RepresentablyFlat (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T) :=
    flat_of_preservesFiniteLimits _
  exact Functor.isContinuous_iff_coverPreserving.mpr
    ((MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T).coverPreserving_restrictedTopology _)


/-- The genuine inclusion of étale covering sieves among fppf covering sieves. -/
theorem etale_le_fppf_over (S : Scheme.{u}) :
    Scheme.etaleTopology.over S ≤ Scheme.fppfTopology.over S := by
  have h : Scheme.etaleTopology ≤ Scheme.fppfTopology :=
    Precoverage.toGrothendieck_mono
      (Scheme.precoverage_mono fun _ _ _ _ ↦ ⟨inferInstance, inferInstance⟩)
  intro T R hR
  rw [GrothendieckTopology.mem_over_iff] at hR ⊢
  exact h _ hR

set_option backward.isDefEq.respectTransparency false in
/-- Relocalization of small étale test schemes is continuous. -/
instance testFunctor_continuous (T : Over S) :
    (testFunctor T).IsContinuous T.left.smallEtaleTopology (Scheme.etaleTopology.over S) :=
  Functor.isContinuous_comp
    (MorphismProperty.Over.forget @AlgebraicGeometry.Etale ⊤ T.left)
    (Over.map T.hom) T.left.smallEtaleTopology (Scheme.etaleTopology.over T.left)
    (Scheme.etaleTopology.over S)

set_option backward.privateInPublic true in
/-- The identity map from a test scheme to the identity étale object over the base. -/
private def identityOverInv (T : Over S) : T ⟶ (testFunctor T).obj (Scheme.Etale.mk (𝟙 T.left)) :=
  Over.homMk (𝟙 T.left) (by
    change 𝟙 T.left ≫ (𝟙 T.left ≫ T.hom) = T.hom
    simp only [Category.id_comp])

/-- Restriction of an étale sheaf to the small étale test site is a sheaf. -/
def targetLocalSheaf (Q : Sheaf (Scheme.etaleTopology.over S) (Type u)) (T : Over S) :
    Sheaf T.left.smallEtaleTopology (Type u) :=
  ((testFunctor T).sheafPushforwardContinuous (Type u)
    T.left.smallEtaleTopology (Scheme.etaleTopology.over S)).obj
      Q

/-- The universal extension to the sheafification on the small étale test site. -/
def descentLift (P : (Over S)ᵒᵖ ⥤ Type u)
    (Q : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : P ⟶ Q.obj) (T : Over S) :
    (localSheaf P T).obj ⟶ restriction Q.obj T :=
  sheafifyLift T.left.smallEtaleTopology
    (Functor.whiskerLeft (testFunctor T).op η) (targetLocalSheaf Q T).property

set_option backward.privateInPublic true in
/-- Evaluation of local descent at the identity test scheme. -/
def descendSection (P : (Over S)ᵒᵖ ⥤ Type u)
    (Q : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : P ⟶ Q.obj) (T : Over S) :
    (localSheaf P T).obj.obj (op (Scheme.Etale.mk (𝟙 T.left))) → Q.obj.obj (op T) :=
  fun q ↦ Q.obj.map (identityOverInv T).op ((descentLift P Q η T).app (op (Scheme.Etale.mk (𝟙 T.left))) q)

/-- The two explicit identity-scheme arrows cancel. -/
private theorem identityOverInv_hom (T : Over S) : identityOverInv T ≫ (identityOverHom (T := T)) = 𝟙 T := by
  apply Over.OverMorphism.ext
  exact Category.id_comp (𝟙 T.left)

set_option backward.privateInPublic true in
/-- The descended operation agrees with the original presheaf map on every generator. -/
theorem descendSection_toSheafify (P : (Over S)ᵒᵖ ⥤ Type u)
    (Q : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : P ⟶ Q.obj)
    (T : Over S) (q : P.obj (op T)) :
    descendSection P Q η T (unitSection P T q) = η.app (op T) q := by
  have h := toSheafify_sheafifyLift T.left.smallEtaleTopology
    (Functor.whiskerLeft (testFunctor T).op η) (targetLocalSheaf Q T).property
  have hq := congrArg (fun k : (restriction P T).obj (op (Scheme.Etale.mk (𝟙 T.left))) ⟶
      (restriction Q.obj T).obj (op (Scheme.Etale.mk (𝟙 T.left))) => k.hom (P.map ((identityOverHom (T := T))).op q))
    (NatTrans.congr_app h (op (Scheme.Etale.mk (𝟙 T.left))))
  change Q.obj.map (identityOverInv T).op
    ((descentLift P Q η T).app (op (Scheme.Etale.mk (𝟙 T.left)))
      ((CategoryTheory.toSheafify T.left.smallEtaleTopology (restriction P T)).app (op (Scheme.Etale.mk (𝟙 T.left)))
        (P.map ((identityOverHom (T := T))).op q))) = _
  rw [show (descentLift P Q η T).app (op (Scheme.Etale.mk (𝟙 T.left)))
      ((CategoryTheory.toSheafify T.left.smallEtaleTopology (restriction P T)).app (op (Scheme.Etale.mk (𝟙 T.left)))
        (P.map ((identityOverHom (T := T))).op q)) =
      η.app (op ((testFunctor T).obj (Scheme.Etale.mk (𝟙 T.left)))) (P.map ((identityOverHom (T := T))).op q) from hq]
  rw [NatTrans.naturality_apply]
  change (Q.obj.map ((identityOverHom (T := T))).op ≫ Q.obj.map (identityOverInv T).op) (η.app (op T) q) = _
  rw [← Q.obj.map_comp, ← op_comp, identityOverInv_hom, op_id, Q.obj.map_id]
  rfl

/-- Descent of identity sections commutes with restriction of test schemes. -/
theorem descendSection_naturality (F : (Over S)ᵒᵖ ⥤ Type u)
    (G : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : F ⟶ G.obj)
    {T T' : Over S} (f : T' ⟶ T) :
    restrictionMap F f ≫ TypeCat.ofHom (descendSection F G η T') =
      TypeCat.ofHom (descendSection F G η T) ≫ G.obj.map f.op := sorry

/-- The morphism from étale sheafification induced by a morphism to an étale sheaf. -/
def desc (F : (Over S)ᵒᵖ ⥤ Type u)
    (G : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : F ⟶ G.obj) :
    sheafify F ⟶ G.obj where
  app T := TypeCat.ofHom (descendSection F G η T.unop)
  naturality := by
    intro X Y f
    exact descendSection_naturality F G η f.unop

/-- The universal property of étale sheafification. -/
theorem universal (F : (Over S)ᵒᵖ ⥤ Type u)
    (G : Sheaf (Scheme.etaleTopology.over S) (Type u)) (η : F ⟶ G.obj) :
    ∃! θ : sheafify F ⟶ G.obj, toSheafify F ≫ θ = η := by
  sorry

end AlgebraicGeometry.Scheme.EtaleSheafification
