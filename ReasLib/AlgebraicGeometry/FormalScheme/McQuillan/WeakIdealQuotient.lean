/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Thickening
public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan.Ideal
public import ReasLib.AlgebraicGeometry.FormalScheme.McQuillan.ChosenFppf.Points

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
  rfl

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
  rfl

/-- The stalks of the sheaf quotient by a weak ideal are local rings. -/
theorem IdealSheafData.quotientSheaf_stalk_isLocalRing {X : FormalScheme.{u}}
    (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I) :
    ∀ x : X.carrier, IsLocalRing (TopCat.Presheaf.stalk (C := CommRingCat.{u}) I.quotientSheaf.obj x) :=
  sorry

/-- The quotient locally ringed space by a weak ideal is locally affine. -/
theorem IdealSheafData.quotientSheaf_local_affine {X : FormalScheme.{u}}
    (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I) :
    ∀ x : X.carrier, ∃ (U : OpenNhds x) (R : CommRingCat.{u}),
      Nonempty
        (({ carrier := X.carrier
            presheaf := I.quotientSheaf.obj
            IsSheaf := I.quotientSheaf.property
            isLocalRing := I.quotientSheaf_stalk_isLocalRing hI } : LocallyRingedSpace).restrict
          U.isOpenEmbedding ≅ Spec.toLocallyRingedSpace.obj (op R)) :=
  sorry

/-- The scheme on the original space with structure sheaf the sheafification
of the sectionwise quotient by a weak ideal of definition. -/
def IdealSheafData.quotientScheme {X : FormalScheme.{u}} (I : IdealSheafData X)
    (hI : IsWeakIdealOfDefinition I) : Scheme.{u} where
  carrier := X.carrier
  presheaf := I.quotientSheaf.obj
  IsSheaf := I.quotientSheaf.property
  isLocalRing := I.quotientSheaf_stalk_isLocalRing hI
  local_affine := I.quotientSheaf_local_affine hI

/-- The underlying space of `quotientScheme I` is the underlying space of `X`. -/
theorem IdealSheafData.quotientScheme_carrier {X : FormalScheme.{u}}
    (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I) :
    (I.quotientScheme hI).carrier = X.carrier :=
  rfl

/-- The structure sheaf of `quotientScheme I` is the sheafification of the
sectionwise quotient presheaf. -/
theorem IdealSheafData.quotientScheme_presheaf {X : FormalScheme.{u}}
    (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I) :
    (I.quotientScheme hI).presheaf = I.quotientSheaf.obj :=
  rfl

/-- On a formal affine open, the sheafification unit of the sectionwise
quotient induces a bijection of underlying section rings. -/
theorem IdealSheafData.quotientPresheaf_toSheafify_bijective {X : FormalScheme.{u}}
    (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I) (U : X.affineOpens) :
    Function.Bijective ((toSheafify (Opens.grothendieckTopology X.carrier)
        I.quotientPresheaf).app (op U.1)).hom :=
  sorry

/-- The quotient projection followed by sheafification is continuous for
pseudo-discrete quotient-scheme sections. -/
theorem IdealSheafData.quotientιC_continuous {X : FormalScheme.{u}}
    (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I)
    (U : (Opens X.carrier)ᵒᵖ) :
    Continuous (X := X.presheaf.obj U)
      (Y := (ofScheme.obj (I.quotientScheme hI)).presheaf.obj U)
      ((CommRingCat.ofHom (Ideal.Quotient.mk (I.idealOn (unop U))) ≫
        (toSheafify (Opens.grothendieckTopology X.carrier) I.quotientPresheaf).app U).hom :
        X.presheaf.obj U → (ofScheme.obj (I.quotientScheme hI)).presheaf.obj U) :=
  sorry

/-- Quotient projections followed by sheafification commute with restriction. -/
theorem IdealSheafData.quotientιC_naturality {X : FormalScheme.{u}}
    (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I)
    {U V : (Opens X.carrier)ᵒᵖ} (g : U ⟶ V) :
    X.presheaf.map g ≫
      (⟨(CommRingCat.ofHom (Ideal.Quotient.mk (I.idealOn (unop V))) ≫
          (toSheafify (Opens.grothendieckTopology X.carrier) I.quotientPresheaf).app V).hom,
        I.quotientιC_continuous hI V⟩ :
        X.presheaf.obj V ⟶ ((𝟙 X.carrier) _*
          (ofScheme.obj (I.quotientScheme hI)).presheaf).obj V) =
      (⟨(CommRingCat.ofHom (Ideal.Quotient.mk (I.idealOn (unop U))) ≫
          (toSheafify (Opens.grothendieckTopology X.carrier) I.quotientPresheaf).app U).hom,
        I.quotientιC_continuous hI U⟩ :
        X.presheaf.obj U ⟶ ((𝟙 X.carrier) _*
          (ofScheme.obj (I.quotientScheme hI)).presheaf).obj U) ≫
        ((𝟙 X.carrier) _* (ofScheme.obj (I.quotientScheme hI)).presheaf).map g :=
  sorry

/-- The sheaf map whose components are quotient projections followed by sheafification. -/
def IdealSheafData.quotientιC {X : FormalScheme.{u}} (I : IdealSheafData X)
    (hI : IsWeakIdealOfDefinition I) :
    X.presheaf ⟶ (𝟙 X.carrier) _* (ofScheme.obj (I.quotientScheme hI)).presheaf where
  app U :=
    ⟨(CommRingCat.ofHom (Ideal.Quotient.mk (I.idealOn (unop U))) ≫
        (toSheafify (Opens.grothendieckTopology X.carrier) I.quotientPresheaf).app U).hom,
      I.quotientιC_continuous hI U⟩
  naturality {U V} g := I.quotientιC_naturality hI g

/-- The canonical quotient morphism is local on underlying ring stalks. -/
theorem IdealSheafData.quotientι_isLocalHom {X : FormalScheme.{u}}
    (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I) :
    ∀ x : X.carrier, IsLocalHom (LocallyTopologicallyRingedSpaceCat.stalkRingHom
      (SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
        (X := (ofScheme.obj (I.quotientScheme hI)).toSheafedSpace)
        (Y := X.toSheafedSpace)
        { base := 𝟙 X.carrier
          c := I.quotientιC hI }) x) :=
  sorry

/-- The obvious morphism of McQuillan formal schemes from
`ofScheme (quotientScheme I)` to `X`, identity on underlying spaces. -/
def IdealSheafData.quotientι {X : FormalScheme.{u}} (I : IdealSheafData X)
    (hI : IsWeakIdealOfDefinition I) :
    ofScheme.obj (I.quotientScheme hI) ⟶ X :=
  CategoryTheory.ObjectProperty.homMk
    (AlgebraicGeometry.LocallyTopologicallyRingedSpaceCat.Hom.ofSheafedHom
      (SheafedSpace.fullyFaithfulForgetToPresheafedSpace.preimage
          { base := 𝟙 X.carrier
            c := (I.quotientιC hI) })
      (I.quotientι_isLocalHom hI))

/-- The underlying continuous map of `quotientι I` is the identity of the
underlying space of `X`. -/
theorem IdealSheafData.quotientι_base {X : FormalScheme.{u}} (I : IdealSheafData X)
    (hI : IsWeakIdealOfDefinition I) :
    (AlgebraicGeometry.McQuillan.FormalScheme.Hom.toLTRSHom (I.quotientι hI)).toSheafedHom.hom.base =
      𝟙 X.carrier :=
  sorry

/-- Components of `quotientι` are the quotient projections followed by the
sheafification unit. -/
theorem IdealSheafData.quotientι_app {X : FormalScheme.{u}} (I : IdealSheafData X)
    (hI : IsWeakIdealOfDefinition I) (U : (Opens X.carrier)ᵒᵖ) :
    ((AlgebraicGeometry.McQuillan.FormalScheme.Hom.toLTRSHom (I.quotientι hI)).toSheafedHom.hom.c.app U).val =
      (CommRingCat.ofHom (Ideal.Quotient.mk (I.idealOn (unop U))) ≫
        (toSheafify (Opens.grothendieckTopology X.carrier) I.quotientPresheaf).app U).hom :=
  sorry

/-- The kernel of `quotientι I` recovers `I`. -/
theorem IdealSheafData.ker_quotientι {X : FormalScheme.{u}} (I : IdealSheafData X)
    (hI : IsWeakIdealOfDefinition I) :
    ∀ U : X.affineOpens,
      RingHom.ker
        ((Hom.toLTRSHom (I.quotientι hI)).toSheafedHom.hom.c.app (op U.1)).val =
        I.ideal U :=
  sorry

/-- The actual kernel ideal sheaf of the canonical quotient morphism is `I`. -/
theorem IdealSheafData.ker_quotientι_eq {X : FormalScheme.{u}} (I : IdealSheafData X)
    (hI : IsWeakIdealOfDefinition I) :
    Hom.ker (I.quotientι hI) = I :=
  IdealSheafData.ext (funext fun U ↦ I.ker_quotientι hI U)

/-- The thickening of `h_X` associated to a weak ideal of definition, obtained
by applying `sheafOfPoints` to `quotientι`. -/
def IdealSheafData.toSchemeThickening (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier) [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X : FormalScheme.{u}} (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I) :
    (sheafOfPoints 𝒮 S).obj (ofScheme.obj (I.quotientScheme hI)) ⟶
      (sheafOfPoints 𝒮 S).obj X :=
  (sheafOfPoints 𝒮 S).map (I.quotientι hI)

/-- `toSchemeThickening` is `sheafOfPoints.map` of `quotientι`. -/
theorem IdealSheafData.toSchemeThickening_eq (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier) [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    {X : FormalScheme.{u}} (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I) :
    I.toSchemeThickening 𝒮 S hI = (sheafOfPoints 𝒮 S).map (I.quotientι hI) :=
  rfl

/-- The sheaf morphism associated to `quotientι I` is a relative thickening on
`(Sch/S)_fppf`. -/
theorem IdealSheafData.quotientι_isThickening (𝒮 : ChosenBigFppfSite.{u, v})
    (S : 𝒮.carrier) [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    {X : FormalScheme.{u}}
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size)
    (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I) :
    IsAffineFormalAlgebraicSpace.isRelativeThickening (I.toSchemeThickening 𝒮 S hI) :=
  sorry

/-- A bounded scheme-source thickening lifts to a formal-scheme morphism. Its
actual structure-sheaf kernel is weak, and its canonical quotient presents the
given source. Only existence is asserted: no data are selected from this theorem. -/
theorem exists_kernel_of_schemeThickening
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    {X : FormalScheme.{u}}
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size)
    (Z : Scheme.{u})
    (hZ : ∃ T : 𝒮.carrier, Z.size ≤ (𝒮.toScheme.obj T).size)
    (i : (sheafOfPoints 𝒮 S).obj (ofScheme.obj Z) ⟶ (sheafOfPoints 𝒮 S).obj X)
    (hi : IsAffineFormalAlgebraicSpace.isRelativeThickening i) :
    ∃ (f : ofScheme.obj Z ⟶ X) (_ : (sheafOfPoints 𝒮 S).map f = i)
      (hI : IsWeakIdealOfDefinition (Hom.ker f))
      (e : (Hom.ker f).quotientScheme hI ≅ Z),
      ofScheme.map e.hom ≫ f = (Hom.ker f).quotientι hI :=
  sorry

/-- Weak ideals produce relative thickenings, and every bounded scheme-source
relative thickening uniquely determines its ideal and quotient presentation. -/
theorem weakIdeal_thickening_correspondence
    {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (hS : IsTerminal (𝒮.toScheme.obj S))
    (h𝒮 : Scheme.IsSmallBoundClosed
      (fun T : Scheme.{u} ↦ ∃ U : 𝒮.carrier, Nonempty (T ≅ 𝒮.toScheme.obj U)))
    {X : FormalScheme.{u}}
    (hsize : ∃ T : 𝒮.carrier, X.size ≤ (𝒮.toScheme.obj T).size) :
    (∀ (I : IdealSheafData X) (hI : IsWeakIdealOfDefinition I),
      IsAffineFormalAlgebraicSpace.isRelativeThickening (I.toSchemeThickening 𝒮 S hI)) ∧
    ∀ (Z : Scheme.{u})
      (hZ : ∃ T : 𝒮.carrier, Z.size ≤ (𝒮.toScheme.obj T).size)
      (i : (sheafOfPoints 𝒮 S).obj (ofScheme.obj Z) ⟶ (sheafOfPoints 𝒮 S).obj X),
      IsAffineFormalAlgebraicSpace.isRelativeThickening i →
        ∃! I : IdealSheafData X, ∃ (hI : IsWeakIdealOfDefinition I)
          (e : I.quotientScheme hI ≅ Z),
          (sheafOfPoints 𝒮 S).map (ofScheme.map e.hom) ≫ i =
            I.toSchemeThickening 𝒮 S hI := by
  constructor
  · intro I hI
    exact I.quotientι_isThickening 𝒮 S hS h𝒮 hsize hI
  · intro Z hZ i hi
    obtain ⟨f, hf, hI, e, he⟩ :=
      exists_kernel_of_schemeThickening hS h𝒮 hsize Z hZ i hi
    refine ⟨Hom.ker f, ⟨hI, e, ?_⟩, ?_⟩
    · rw [← hf, ← (sheafOfPoints 𝒮 S).map_comp, he]
      rfl
    · intro J hJ
      sorry

end AlgebraicGeometry.McQuillan.FormalScheme
