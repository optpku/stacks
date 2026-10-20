/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_Ideal
public import stacks_project.Chap87.Remark_87_13_3_Weak_ideals_of_definition_Points

/-!
# Quotient schemes of weak ideals of definition

A weak ideal of definition `I` on a McQuillan formal scheme `X` determines the
scheme `Z = (X, O_X / I)` on the same underlying space, together with the
obvious morphism `ofScheme.obj Z ⟶ X` whose kernel recovers `I`.
-/

@[expose] public section

universe u v

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite TopologicalRing

namespace AlgebraicGeometry.McQuillan.FormalScheme

/-- The sectionwise quotient of `O_X` by an ideal sheaf, as a presheaf of
commutative rings on the underlying space of `X`. -/
def IdealSheafData.quotientPresheaf {X : FormalScheme.{u}} (I : IdealSheafData X) :
    X.carrier.Presheaf CommRingCat.{u} where
  obj U := CommRingCat.of ((X.presheaf.obj U : Type u) ⧸ I.idealOn (unop U))
  map {U V} f :=
    CommRingCat.ofHom
      (Ideal.quotientMap (I.idealOn (unop V)) (X.presheaf.map f).val (by
        intro s hs
        change (X.presheaf.map f).val s ∈ I.idealOn (unop V)
        simp only [IdealSheafData.idealOn, Submodule.mem_iInf, Ideal.mem_comap] at hs ⊢
        intro W hW
        have hcomp : f ≫ (homOfLE hW).op =
            (homOfLE (hW.trans (leOfHom f.unop))).op := Subsingleton.elim _ _
        change (X.presheaf.map f ≫ X.presheaf.map (homOfLE hW).op).val s ∈ I.ideal W
        rw [← X.presheaf.map_comp, hcomp]
        exact hs W (hW.trans (leOfHom f.unop))))
  map_id U := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    simp only [CommRingCat.hom_ofHom, CommRingCat.hom_id, RingHom.id_apply,
      Ideal.quotientMap_mk, X.presheaf.map_id]
    rfl
  map_comp f g := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective s
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      Ideal.quotientMap_mk, X.presheaf.map_comp]
    rfl

/-- On objects, `quotientPresheaf` is the sectionwise quotient by `idealOn`. -/
theorem IdealSheafData.quotientPresheaf_obj {X : FormalScheme.{u}}
    (I : IdealSheafData X) (U : (Opens X.carrier)ᵒᵖ) :
    I.quotientPresheaf.obj U =
      CommRingCat.of ((X.presheaf.obj U : Type u) ⧸ I.idealOn (unop U)) :=
  sorry

/-- The sheafification of the sectionwise quotient of `O_X` by `I`. -/
def IdealSheafData.quotientSheaf {X : FormalScheme.{u}} (I : IdealSheafData X) :
    TopCat.Sheaf CommRingCat.{u} X.carrier :=
  (presheafToSheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).obj
    I.quotientPresheaf

/-- `quotientSheaf` is `presheafToSheaf` of the sectionwise quotient presheaf. -/
theorem IdealSheafData.quotientSheaf_eq {X : FormalScheme.{u}} (I : IdealSheafData X) :
    I.quotientSheaf =
      (presheafToSheaf (Opens.grothendieckTopology X.carrier) CommRingCat.{u}).obj
        I.quotientPresheaf :=
  sorry

/-- The scheme `Z = (X, O_X / I)` associated to a weak ideal of definition, with
the same underlying space as `X` and structure sheaf the sheafification of the
sectionwise quotient. -/
def IdealSheafData.quotientScheme {X : FormalScheme.{u}} (I : IdealSheafData X)
    [IsWeakIdealOfDefinition I] : Scheme.{u} where
  carrier := X.carrier
  presheaf := I.quotientSheaf.obj
  IsSheaf := I.quotientSheaf.property
  isLocalRing := sorry
  local_affine := sorry

/-- The underlying space of `quotientScheme I` is the underlying space of `X`. -/
theorem IdealSheafData.quotientScheme_carrier {X : FormalScheme.{u}}
    (I : IdealSheafData X) [IsWeakIdealOfDefinition I] :
    I.quotientScheme.carrier = X.carrier :=
  sorry

/-- The structure sheaf of `quotientScheme I` is the sheafification of the
sectionwise quotient presheaf. -/
theorem IdealSheafData.quotientScheme_presheaf {X : FormalScheme.{u}}
    (I : IdealSheafData X) [IsWeakIdealOfDefinition I] :
    I.quotientScheme.presheaf = I.quotientSheaf.obj :=
  sorry

/-- On a formal affine open, the sheafification unit of the sectionwise
quotient is an isomorphism. -/
theorem IdealSheafData.instIsIso_toSheafify_app {X : FormalScheme.{u}}
    (I : IdealSheafData X) [IsWeakIdealOfDefinition I] (U : X.affineOpens) :
    IsIso ((toSheafify (Opens.grothendieckTopology X.carrier)
        I.quotientPresheaf).app (op U.1)) :=
  sorry

/-- The sheaf map of the obvious morphism `ofScheme (quotientScheme I) ⟶ X`,
given on sections by the quotient projections followed by sheafification. -/
def IdealSheafData.quotientιC {X : FormalScheme.{u}} (I : IdealSheafData X)
    [IsWeakIdealOfDefinition I] :
    X.presheaf ⟶ (𝟙 X.carrier) _* (ofScheme.obj I.quotientScheme).presheaf where
  app U :=
    ⟨(CommRingCat.ofHom (Ideal.Quotient.mk (I.idealOn (unop U))) ≫
        (toSheafify (Opens.grothendieckTopology X.carrier) I.quotientPresheaf).app U).hom,
      sorry⟩
  naturality := sorry

/-- The obvious morphism of McQuillan formal schemes from
`ofScheme (quotientScheme I)` to `X`, identity on underlying spaces. -/
def IdealSheafData.quotientι {X : FormalScheme.{u}} (I : IdealSheafData X)
    [IsWeakIdealOfDefinition I] :
    ofScheme.obj I.quotientScheme ⟶ X :=
  CategoryTheory.ObjectProperty.homMk
    (AlgebraicGeometry.LocallyTopologicallyRingedSpaceCat.Hom.ofSheafedHom
      (SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
          { base := 𝟙 X.carrier
            c := I.quotientιC })
      (fun _ ↦ sorry))

/-- The underlying continuous map of `quotientι I` is the identity of the
underlying space of `X`. -/
theorem IdealSheafData.quotientι_base {X : FormalScheme.{u}} (I : IdealSheafData X)
    [IsWeakIdealOfDefinition I] :
    (AlgebraicGeometry.McQuillan.FormalScheme.Hom.toLTRSHom I.quotientι).toSheafedHom.hom.base =
      𝟙 X.carrier :=
  sorry

/-- Components of `quotientι` are the quotient projections followed by the
sheafification unit. -/
theorem IdealSheafData.quotientι_app {X : FormalScheme.{u}} (I : IdealSheafData X)
    [IsWeakIdealOfDefinition I] (U : (Opens X.carrier)ᵒᵖ) :
    ((AlgebraicGeometry.McQuillan.FormalScheme.Hom.toLTRSHom I.quotientι).toSheafedHom.hom.c.app U).val =
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.idealOn (unop U))) ≫
        (toSheafify (Opens.grothendieckTopology X.carrier) I.quotientPresheaf).app U).hom :=
  sorry

/-- The kernel ideal sheaf of a morphism of McQuillan formal schemes, recorded
on formal affine opens of the target. -/
def IdealSheafData.ker {Y X : FormalScheme.{u}} (f : Y ⟶ X) : IdealSheafData X where
  ideal U := RingHom.ker
    ((AlgebraicGeometry.McQuillan.FormalScheme.Hom.toLTRSHom f).toSheafedHom.hom.c.app (op U.1)).val
  map_ideal := sorry

/-- On a formal affine open, `ker f` is the kernel of the component ring
homomorphism of `f`. -/
theorem IdealSheafData.ker_spec {Y X : FormalScheme.{u}} (f : Y ⟶ X)
    (U : X.affineOpens) :
    (IdealSheafData.ker f).ideal U =
      RingHom.ker
        ((AlgebraicGeometry.McQuillan.FormalScheme.Hom.toLTRSHom f).toSheafedHom.hom.c.app (op U.1)).val :=
  sorry

/-- The kernel of `quotientι I` recovers `I`. -/
theorem IdealSheafData.ker_quotientι {X : FormalScheme.{u}} (I : IdealSheafData X)
    [IsWeakIdealOfDefinition I] :
    IdealSheafData.ker I.quotientι = I :=
  sorry

/-- The thickening of `h_X` associated to a weak ideal of definition, obtained
by applying `sheafOfPoints` to `quotientι`. -/
def IdealSheafData.toSchemeThickening (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier) [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X : FormalScheme.{u}} (I : IdealSheafData X) [IsWeakIdealOfDefinition I] :
    (sheafOfPoints 𝒮 S).obj (ofScheme.obj I.quotientScheme) ⟶
      (sheafOfPoints 𝒮 S).obj X :=
  (sheafOfPoints 𝒮 S).map I.quotientι

/-- `toSchemeThickening` is `sheafOfPoints.map` of `quotientι`. -/
theorem IdealSheafData.toSchemeThickening_eq (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier) [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X : FormalScheme.{u}} (I : IdealSheafData X) [IsWeakIdealOfDefinition I] :
    I.toSchemeThickening 𝒮 S = (sheafOfPoints 𝒮 S).map I.quotientι :=
  sorry

/-- The sheaf morphism associated to `quotientι I` is a relative thickening on
`(Sch/S)_fppf`. -/
theorem IdealSheafData.quotientι_isThickening (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier) [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : FormalScheme.{u}} (I : IdealSheafData X) [IsWeakIdealOfDefinition I] :
    (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor
      (I.toSchemeThickening 𝒮 S) :=
  sorry

/-- The weak ideal of definition recovered from a McQuillan morphism
`ofScheme.obj Z ⟶ X`. -/
def IdealSheafData.ofSchemeThickening {X : FormalScheme.{u}} (Z : Scheme.{u})
    (i : ofScheme.obj Z ⟶ X) : IdealSheafData X :=
  IdealSheafData.ker i

/-- `ofSchemeThickening` is the kernel ideal sheaf of `i`. -/
theorem IdealSheafData.ofSchemeThickening_eq {X : FormalScheme.{u}} (Z : Scheme.{u})
    (i : ofScheme.obj Z ⟶ X) :
    IdealSheafData.ofSchemeThickening Z i = IdealSheafData.ker i :=
  sorry

/-- Starting from a weak ideal of definition, the kernel of `quotientι`
recovers the same ideal sheaf. -/
theorem IdealSheafData.ofSchemeThickening_toSchemeThickening {X : FormalScheme.{u}}
    (I : IdealSheafData X) [IsWeakIdealOfDefinition I] :
    IdealSheafData.ofSchemeThickening I.quotientScheme I.quotientι = I :=
  sorry

/-- Starting from a relative thickening of `h_X`, the kernel is a weak ideal of
definition and the quotient scheme recovers `Z` over `X`. -/
theorem IdealSheafData.quotientScheme_ofSchemeThickening
    (𝒮 : ChosenBigFppfSite.{u, v}) (S : 𝒮.carrier)
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X : FormalScheme.{u}} {Z : Scheme.{u}} (i : ofScheme.obj Z ⟶ X)
    (hi : (MorphismProperty.inverseImage (@IsThickening) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor
      ((sheafOfPoints 𝒮 S).map i)) :
    ∃ (hI : IsWeakIdealOfDefinition (IdealSheafData.ker i))
      (e : @IdealSheafData.quotientScheme _ (IdealSheafData.ker i) hI ≅ Z),
      ofScheme.map e.hom ≫ i =
        @IdealSheafData.quotientι _ (IdealSheafData.ker i) hI :=
  sorry

end AlgebraicGeometry.McQuillan.FormalScheme
