/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
public import Mathlib.Topology.Sheaves.MayerVietoris
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.CategoryTheory.ComposableArrows.ZeroPrecomp.Functor
public import ReasLib.CategoryTheory.Sites.Cohomology.Map
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Mayer--Vietoris cohomology for ringed spaces

This leaf owns the ringed-space view of the site-theoretic Mayer--Vietoris sequence.  The
underlying additive sheaf is the canonical forgetful view of an `𝒪_X`-module; the union
identification is recorded by an explicit cohomology isomorphism rather than by a local
instance or a hidden rewrite.  The sequence map and its functoriality are separate owners so
later arguments can use only the part of the API they need.
-/

open CategoryTheory
open CategoryTheory.ComposableArrows
open CategoryTheory.Limits
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- The underlying additive sheaf of a module on `X`. -/
abbrev underlying (F : X.Modules) : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (moduleUnderlyingSheaf X).obj F

/-- The Mayer--Vietoris square of two opens of `X`. -/
@[stacks 01EB "Mayer--Vietoris square of two opens"]
noncomputable abbrev square (U V : Opens X.carrier) :
    (Opens.grothendieckTopology X).MayerVietorisSquare :=
  Opens.mayerVietorisSquare U V

/-- The cohomology isomorphism induced by a cover equation `U ⊔ V = ⊤`. -/
@[stacks 01EB "cohomology transport along the union identification"]
noncomputable abbrev unionIso (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) (n : ℕ) :
    (underlying F).H' n (U ⊔ V) ≅ (underlying F).H' n ⊤ :=
  (underlying F).cohomologyPresheaf n |>.mapIso (eqToIso hUV).symm.op

/-- The five-arrow Mayer--Vietoris segment for a cover of `X` by `U` and `V`, with the union
term transported to the global cohomology term. -/
@[stacks 01EB "Mayer--Vietoris sequence for module cohomology"]
noncomputable def sequence (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) (n : ℕ) : ComposableArrows AddCommGrpCat.{u} 5 :=
  ComposableArrows.mk₅
    ((unionIso U V hUV F n).inv ≫
      (Opens.mayerVietorisSquare U V).toBiprod (underlying F) n)
    ((Opens.mayerVietorisSquare U V).fromBiprod (underlying F) n)
    ((Opens.mayerVietorisSquare U V).δ (underlying F) n (n + 1) rfl ≫
      (unionIso U V hUV F (n + 1)).hom)
    ((unionIso U V hUV F (n + 1)).inv ≫
      (Opens.mayerVietorisSquare U V).toBiprod (underlying F) (n + 1))
    ((Opens.mayerVietorisSquare U V).fromBiprod (underlying F) (n + 1))

set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the five-arrow Mayer--Vietoris segment. -/
@[stacks 01EB "exactness of the Mayer--Vietoris segment"]
theorem sequence_exact (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) (n : ℕ) :
    (sequence U V hUV F n).Exact := by
  let S := Opens.mayerVietorisSquare U V
  let e : S.sequence (underlying F) n (n + 1) rfl ≅ sequence U V hUV F n :=
    isoMk₅ (unionIso U V hUV F n) (Iso.refl _) (Iso.refl _)
      (unionIso U V hUV F (n + 1)) (Iso.refl _) (Iso.refl _)
      (by
        change S.toBiprod (underlying F) n ≫ 𝟙 _ =
          (unionIso U V hUV F n).hom ≫
            ((unionIso U V hUV F n).inv ≫ S.toBiprod (underlying F) n)
        simp only [Category.comp_id, Iso.hom_inv_id_assoc])
      (by
        change S.fromBiprod (underlying F) n ≫ 𝟙 _ =
          𝟙 _ ≫ S.fromBiprod (underlying F) n
        simp only [Category.comp_id, Category.id_comp])
      (by
        change S.δ (underlying F) n (n + 1) rfl ≫ (unionIso U V hUV F (n + 1)).hom =
          𝟙 _ ≫ (S.δ (underlying F) n (n + 1) rfl ≫ (unionIso U V hUV F (n + 1)).hom)
        rw [Category.id_comp])
      (by
        change S.toBiprod (underlying F) (n + 1) ≫ 𝟙 _ =
          (unionIso U V hUV F (n + 1)).hom ≫
            ((unionIso U V hUV F (n + 1)).inv ≫ S.toBiprod (underlying F) (n + 1))
        simp only [Category.comp_id, Iso.hom_inv_id_assoc])
      (by
        change S.fromBiprod (underlying F) (n + 1) ≫ 𝟙 _ =
          𝟙 _ ≫ S.fromBiprod (underlying F) (n + 1)
        simp only [Category.comp_id, Category.id_comp])
  exact exact_of_iso e (S.sequence_exact (underlying F) n (n + 1) rfl)

/-- The cohomology map on an open induced by a morphism of modules. -/
@[stacks 01EB "cohomology map on an open"]
noncomputable abbrev mapAt {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (W : Opens X.carrier) :
    (underlying F).H' n W ⟶ (underlying G).H' n W :=
  CategoryTheory.Sheaf.cohomologyMap ((moduleUnderlyingSheaf X).map φ) n W

/-- The map on the two-open biproduct induced by a module morphism. -/
@[stacks 01EB "biproduct cohomology map on two opens"]
noncomputable abbrev mapBiprod {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    (U V : Opens X.carrier) :
    (underlying F).H' n U ⊞ (underlying F).H' n V ⟶
      (underlying G).H' n U ⊞ (underlying G).H' n V :=
  biprod.map (mapAt φ n U) (mapAt φ n V)

private theorem mapAt_naturality {F G : X.Modules} (φ : F ⟶ G) (n : ℕ)
    {W W' : Opens X.carrier} (i : W ⟶ W') :
    ((underlying F).cohomologyPresheaf n).map i.op ≫ mapAt φ n W =
      mapAt φ n W' ≫ ((underlying G).cohomologyPresheaf n).map i.op :=
  ((Sheaf.cohomologyPresheafFunctor.{u} _ n).map
    ((moduleUnderlyingSheaf X).map φ)).naturality i.op

set_option backward.isDefEq.respectTransparency false in
private theorem toBiprod_naturality {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (n : ℕ) :
    (Opens.mayerVietorisSquare U V).toBiprod (underlying F) n ≫ mapBiprod φ n U V =
      mapAt φ n (U ⊔ V) ≫ (Opens.mayerVietorisSquare U V).toBiprod (underlying G) n := by
  change biprod.lift
      (((underlying F).cohomologyPresheaf n).map (homOfLE le_sup_left : U ⟶ U ⊔ V).op)
      (((underlying F).cohomologyPresheaf n).map (homOfLE le_sup_right : V ⟶ U ⊔ V).op) ≫
        biprod.map (mapAt φ n U) (mapAt φ n V) =
    mapAt φ n (U ⊔ V) ≫ biprod.lift
      (((underlying G).cohomologyPresheaf n).map (homOfLE le_sup_left : U ⟶ U ⊔ V).op)
      (((underlying G).cohomologyPresheaf n).map (homOfLE le_sup_right : V ⟶ U ⊔ V).op)
  apply biprod.hom_ext
  · simpa only [Category.assoc, biprod.map_fst, biprod.lift_fst,
      biprod.lift_fst_assoc] using mapAt_naturality φ n (homOfLE le_sup_left : U ⟶ U ⊔ V)
  · simpa only [Category.assoc, biprod.map_snd, biprod.lift_snd,
      biprod.lift_snd_assoc] using mapAt_naturality φ n (homOfLE le_sup_right : V ⟶ U ⊔ V)

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the first arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_zero {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 0 1 ≫ mapBiprod φ n U V =
      mapAt φ n ⊤ ≫ (sequence U V hUV G n).map' 0 1 := by
  change ((unionIso U V hUV F n).inv ≫
    (Opens.mayerVietorisSquare U V).toBiprod (underlying F) n) ≫ mapBiprod φ n U V =
      mapAt φ n ⊤ ≫ ((unionIso U V hUV G n).inv ≫
        (Opens.mayerVietorisSquare U V).toBiprod (underlying G) n)
  rw [Category.assoc, toBiprod_naturality φ U V n, ← Category.assoc]
  exact congrArg (fun f ↦ f ≫ (Opens.mayerVietorisSquare U V).toBiprod (underlying G) n)
    (mapAt_naturality φ n (eqToHom hUV))

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the second arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_one {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 1 2 ≫ mapAt φ n (U ⊓ V) =
      mapBiprod φ n U V ≫ (sequence U V hUV G n).map' 1 2 := by
  change biprod.desc
      (((underlying F).cohomologyPresheaf n).map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)
      (-((underlying F).cohomologyPresheaf n).map (homOfLE inf_le_right : U ⊓ V ⟶ V).op) ≫
        mapAt φ n (U ⊓ V) = biprod.map (mapAt φ n U) (mapAt φ n V) ≫ biprod.desc
      (((underlying G).cohomologyPresheaf n).map (homOfLE inf_le_left : U ⊓ V ⟶ U).op)
      (-((underlying G).cohomologyPresheaf n).map (homOfLE inf_le_right : U ⊓ V ⟶ V).op)
  apply biprod.hom_ext'
  · simpa only [Category.assoc, biprod.inl_desc_assoc, biprod.inl_desc,
      biprod.inl_map_assoc] using mapAt_naturality φ n (homOfLE inf_le_left : U ⊓ V ⟶ U)
  · simpa only [Category.assoc, biprod.inr_desc_assoc, biprod.inr_desc, biprod.inr_map_assoc,
      Preadditive.neg_comp, Preadditive.comp_neg] using congrArg Neg.neg
      (mapAt_naturality φ n (homOfLE inf_le_right : U ⊓ V ⟶ V))

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the connecting arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_two {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 2 3 ≫ mapAt φ (n + 1) ⊤ =
      mapAt φ n (U ⊓ V) ≫ (sequence U V hUV G n).map' 2 3 := by
  let S := Opens.mayerVietorisSquare U V
  have hδ : S.δ (underlying F) n (n + 1) rfl ≫ mapAt φ (n + 1) (U ⊔ V) =
      mapAt φ n (U ⊓ V) ≫ S.δ (underlying G) n (n + 1) rfl := by
    ext x
    change (S.shortComplex_shortExact.extClass.comp x (by omega)).comp
        (Abelian.Ext.mk₀ ((moduleUnderlyingSheaf X).map φ)) (add_zero _) =
      S.shortComplex_shortExact.extClass.comp
        (x.comp (Abelian.Ext.mk₀ ((moduleUnderlyingSheaf X).map φ)) (add_zero _)) (by omega)
    exact Abelian.Ext.comp_assoc_of_third_deg_zero _ _ _ (by omega)
  have hI : (unionIso U V hUV F (n + 1)).hom ≫ mapAt φ (n + 1) ⊤ =
      mapAt φ (n + 1) (U ⊔ V) ≫ (unionIso U V hUV G (n + 1)).hom :=
    mapAt_naturality φ (n + 1) (eqToHom hUV.symm)
  change (S.δ (underlying F) n (n + 1) rfl ≫ (unionIso U V hUV F (n + 1)).hom) ≫
    mapAt φ (n + 1) ⊤ = mapAt φ n (U ⊓ V) ≫
      (S.δ (underlying G) n (n + 1) rfl ≫ (unionIso U V hUV G (n + 1)).hom)
  rw [Category.assoc, hI, ← Category.assoc, hδ, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the fourth arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_three {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 3 4 ≫ mapBiprod φ (n + 1) U V =
      mapAt φ (n + 1) ⊤ ≫ (sequence U V hUV G n).map' 3 4 := by
  change ((unionIso U V hUV F (n + 1)).inv ≫
      (Opens.mayerVietorisSquare U V).toBiprod (underlying F) (n + 1)) ≫
        mapBiprod φ (n + 1) U V =
    mapAt φ (n + 1) ⊤ ≫ ((unionIso U V hUV G (n + 1)).inv ≫
      (Opens.mayerVietorisSquare U V).toBiprod (underlying G) (n + 1))
  have h := map_naturality_zero φ U V hUV (n + 1)
  change ((unionIso U V hUV F (n + 1)).inv ≫
      (Opens.mayerVietorisSquare U V).toBiprod (underlying F) (n + 1)) ≫
        mapBiprod φ (n + 1) U V =
    mapAt φ (n + 1) ⊤ ≫ ((unionIso U V hUV G (n + 1)).inv ≫
      (Opens.mayerVietorisSquare U V).toBiprod (underlying G) (n + 1)) at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the fifth arrow in the Mayer--Vietoris segment. -/
theorem map_naturality_four {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    (sequence U V hUV F n).map' 4 5 ≫ mapAt φ (n + 1) (U ⊓ V) =
      mapBiprod φ (n + 1) U V ≫ (sequence U V hUV G n).map' 4 5 := by
  change (Opens.mayerVietorisSquare U V).fromBiprod (underlying F) (n + 1) ≫
    mapAt φ (n + 1) (U ⊓ V) = mapBiprod φ (n + 1) U V ≫
      (Opens.mayerVietorisSquare U V).fromBiprod (underlying G) (n + 1)
  have h := map_naturality_one φ U V hUV (n + 1)
  change (Opens.mayerVietorisSquare U V).fromBiprod (underlying F) (n + 1) ≫
    mapAt φ (n + 1) (U ⊓ V) = mapBiprod φ (n + 1) U V ≫
      (Opens.mayerVietorisSquare U V).fromBiprod (underlying G) (n + 1) at h
  exact h

/-- The morphism of Mayer--Vietoris segments induced by a module morphism. -/
@[stacks 01EB "morphism of Mayer--Vietoris segments"]
noncomputable def sequenceMap {F G : X.Modules} (φ : F ⟶ G)
    (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    sequence U V hUV F n ⟶ sequence U V hUV G n :=
  homMk₅ (mapAt φ n ⊤) (mapBiprod φ n U V) (mapAt φ n (U ⊓ V))
    (mapAt φ (n + 1) ⊤) (mapBiprod φ (n + 1) U V)
    (mapAt φ (n + 1) (U ⊓ V))
    (map_naturality_zero φ U V hUV n)
    (map_naturality_one φ U V hUV n)
    (map_naturality_two φ U V hUV n)
    (map_naturality_three φ U V hUV n)
    (map_naturality_four φ U V hUV n)

set_option backward.isDefEq.respectTransparency false in
/-- The segment map induced by an identity morphism is the identity. -/
@[stacks 01EB "identity law for Mayer--Vietoris segment maps"]
theorem sequenceMap_id (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) (n : ℕ) :
    sequenceMap (𝟙 F) U V hUV n = 𝟙 _ := by
  have hid (m : ℕ) (W : Opens X.carrier) : mapAt (𝟙 F) m W = 𝟙 _ := by
    dsimp only [mapAt, Sheaf.cohomologyMap]
    rw [(moduleUnderlyingSheaf X).map_id, (Sheaf.cohomologyPresheafFunctor.{u} _ m).map_id]
    rfl
  have hB (m : ℕ) : mapBiprod (𝟙 F) m U V = 𝟙 _ := by
    apply biprod.hom_ext <;> simp [mapBiprod, hid]
  apply hom_ext₅
  · exact hid n ⊤
  · exact hB n
  · exact hid n (U ⊓ V)
  · exact hid (n + 1) ⊤
  · exact hB (n + 1)
  · exact hid (n + 1) (U ⊓ V)

set_option backward.isDefEq.respectTransparency false in
/-- Segment maps respect composition of module morphisms. -/
@[stacks 01EB "composition law for Mayer--Vietoris segment maps"]
theorem sequenceMap_comp (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H) (n : ℕ) :
    sequenceMap (φ ≫ ψ) U V hUV n =
      sequenceMap φ U V hUV n ≫ sequenceMap ψ U V hUV n := by
  have hcomp (m : ℕ) (W : Opens X.carrier) :
      mapAt (φ ≫ ψ) m W = mapAt φ m W ≫ mapAt ψ m W := by
    dsimp only [mapAt, Sheaf.cohomologyMap]
    rw [(moduleUnderlyingSheaf X).map_comp, (Sheaf.cohomologyPresheafFunctor.{u} _ m).map_comp]
    rfl
  have hB (m : ℕ) :
      mapBiprod (φ ≫ ψ) m U V = mapBiprod φ m U V ≫ mapBiprod ψ m U V := by
    apply biprod.hom_ext <;> simp [mapBiprod, hcomp, Category.assoc]
  apply hom_ext₅
  · exact hcomp n ⊤
  · exact hB n
  · exact hcomp n (U ⊓ V)
  · exact hcomp (n + 1) ⊤
  · exact hB (n + 1)
  · exact hcomp (n + 1) (U ⊓ V)

/-- The Mayer--Vietoris segment as a functor of the coefficient module. -/
@[stacks 01EB "functorial Mayer--Vietoris segment"]
noncomputable def functor (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤) (n : ℕ) :
    X.Modules ⥤ ComposableArrows AddCommGrpCat.{u} 5 where
  obj F := sequence U V hUV F n
  map φ := sequenceMap φ U V hUV n
  map_id F := sequenceMap_id U V hUV F n
  map_comp φ ψ := sequenceMap_comp U V hUV φ ψ n

/-- Prefix the degree-zero Mayer--Vietoris segment by the zero morphism. -/
@[stacks 01EB "augmented Mayer--Vietoris segment"]
noncomputable abbrev augmented (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) : ComposableArrows AddCommGrpCat.{u} 6 :=
  (sequence U V hUV F 0).zeroPrecomp 1

open scoped ZeroObject in
set_option backward.isDefEq.respectTransparency false in
/-- Exactness of the degree-zero augmented Mayer--Vietoris segment beginning with `0`. -/
@[stacks 01EB "exactness of the augmented Mayer--Vietoris segment"]
theorem augmented_exact (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (F : X.Modules) :
    (augmented U V hUV F).Exact := by
  let S := Opens.mayerVietorisSquare U V
  haveI hmono : Mono (S.toBiprod (underlying F) 0) := by
    apply (AddCommGrpCat.mono_iff_injective _).2
    intro x y hxy
    apply Abelian.Ext.precomp_mk₀_injective_of_epi (underlying F) S.shortComplex.g
    change (Abelian.Ext.mk₀ S.shortComplex.g).comp x (zero_add 0) =
      (Abelian.Ext.mk₀ S.shortComplex.g).comp y (zero_add 0)
    rw [← S.biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply,
      ← S.biprodAddEquiv_symm_biprodIsoProd_hom_toBiprod_apply, hxy]
  haveI : Mono ((sequence U V hUV F 0).map' 0 1) := by
    change Mono ((unionIso U V hUV F 0).inv ≫ S.toBiprod (underlying F) 0)
    infer_instance
  change ((sequence U V hUV F 0).precomp (0 : (0 : AddCommGrpCat.{u}) ⟶ _)).Exact
  apply exact_of_δ₀
  · apply exact₂_mk _ (by
      change (0 : (0 : AddCommGrpCat.{u}) ⟶ _) ≫ _ = 0
      exact zero_comp)
    apply (ShortComplex.exact_iff_mono _ (by rfl)).2
    change Mono ((sequence U V hUV F 0).map' 0 1)
    infer_instance
  · simpa only [augmented, zeroPrecomp, precomp_δ₀] using sequence_exact U V hUV F 0

/-- The degree-zero augmented Mayer--Vietoris segment as a functor of the coefficient module. -/
@[stacks 01EB "functorial augmented Mayer--Vietoris segment"]
noncomputable abbrev augmentedFunctor (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    : X.Modules ⥤ ComposableArrows AddCommGrpCat.{u} 6 :=
  functor U V hUV 0 ⋙ ComposableArrows.zeroPrecomp.functor 1

end AlgebraicGeometry.RingedSpace.Module.Cohomology.MayerVietoris
