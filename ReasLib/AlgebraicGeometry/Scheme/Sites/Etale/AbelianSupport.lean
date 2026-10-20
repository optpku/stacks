/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionSupport

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

@[expose] public section

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

variable {S : Scheme.{u}}

/-- The additive-group object obtained by taking the small-étale presheaf fiber of an
abelian sheaf at a geometric point of `S`. -/
noncomputable def geometricStalk
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    (sbar : Scheme.GeometricPoint S) : AddCommGrpCat.{u} :=
  (@Scheme.pointSmallEtale S sbar.K inferInstance
    (@IsSepClosed.of_isAlgClosed sbar.K inferInstance sbar.isAlgClosed) sbar.hom).presheafFiber.obj F.1

/-- Geometric stalks have the same zero-object property for geometric points with the same image.
-/
theorem geometricStalk_isZero_iff_of_image_eq
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    (sbar tbar : Scheme.GeometricPoint S)
    (himage : sbar.image = tbar.image) :
    IsZero (geometricStalk F sbar) ↔ IsZero (geometricStalk F tbar) := sorry

/-- The support of an abelian sheaf on the small étale site, as the points admitting a
geometric point with nonzero geometric stalk. -/
noncomputable def abelianSheafSupport
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) : Set S :=
  {s | ∃ sbar : Scheme.GeometricPoint S,
    sbar.image = s ∧ ¬ IsZero (geometricStalk F sbar)}

/-- Membership in the étale abelian-sheaf support is existence of a geometric point over the
point with nonzero geometric stalk. -/
theorem mem_abelianSheafSupport_iff
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (s : S) :
    s ∈ abelianSheafSupport F ↔
      ∃ sbar : Scheme.GeometricPoint S,
        sbar.image = s ∧ ¬ IsZero (geometricStalk F sbar) := sorry

/-- For any geometric point, support membership is equivalent to nonvanishing of its geometric
stalk; this is independent of the chosen geometric point over the same scheme point. -/
theorem mem_abelianSheafSupport_iff_geometricStalk
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u})
    (sbar : Scheme.GeometricPoint S) :
    sbar.image ∈ abelianSheafSupport F ↔ ¬ IsZero (geometricStalk F sbar) := sorry

/-- The canonical largest Zariski open on which an étale section vanishes, represented as the
supremum of all vanishing opens. -/
noncomputable def largestVanishingOpen
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) : U.left.Opens :=
  sSup {W : U.left.Opens | vanishesOn F U σ W}

/-- The section vanishes on the canonical largest vanishing open. -/
theorem largestVanishingOpen_spec
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) :
    vanishesOn F U σ (largestVanishingOpen F U σ) := sorry

/-- Every open on which the section vanishes is contained in the canonical largest vanishing
open. -/
theorem le_largestVanishingOpen
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) (V : U.left.Opens) :
    vanishesOn F U σ V → V ≤ largestVanishingOpen F U σ := sorry

/-- The support of an étale section, as the bundled closed complement of its largest vanishing
open. -/
noncomputable def abelianSheafSectionSupport
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) : TopologicalSpace.Closeds U.left :=
  TopologicalSpace.Opens.compl (largestVanishingOpen F U σ)

/-- The closed support of a section is the complement of its canonical largest vanishing open. -/
theorem abelianSheafSectionSupport_def
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) :
    abelianSheafSectionSupport F U σ =
      TopologicalSpace.Opens.compl (largestVanishingOpen F U σ) := sorry

/-- A geometric point of `U` lies in the section support exactly when the corresponding geometric
germ of the section is nonzero. -/
theorem mem_abelianSheafSectionSupport_iff
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) (ū : Scheme.GeometricPoint U.left) :
    ū.image ∈ abelianSheafSectionSupport F U σ ↔
      geometricGerm U F σ ū ≠ 0 := sorry

/-- The support of a section of an abelian sheaf on the small étale site is closed
in the underlying scheme of its étale object. -/
theorem isClosed_abelianSheafSectionSupport
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ : F.1.obj (op U)) :
    IsClosed (abelianSheafSectionSupport F U σ : Set U.left) := sorry

/-- The support of a sum of sections is contained in the union of their supports. -/
theorem abelianSheafSectionSupport_add_subset
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) (U : S.Etale)
    (σ σ' : F.1.obj (op U)) :
    (abelianSheafSectionSupport F U (σ + σ') : Set U.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left) ∪
        (abelianSheafSectionSupport F U σ' : Set U.left) := sorry

/-- A morphism of abelian sheaves cannot enlarge the support of a local section. -/
theorem abelianSheafSectionSupport_map_subset
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G)
    (U : S.Etale) (σ : F.1.obj (op U)) :
    (abelianSheafSectionSupport G U (φ.hom.app (op U) σ) : Set U.left) ⊆
      (abelianSheafSectionSupport F U σ : Set U.left) := sorry

/-- The support of an abelian sheaf is the union of the images of the supports of
all its local sections. -/
theorem abelianSheafSupport_eq_iUnion_sectionSupport
    (F : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}) :
    abelianSheafSupport F =
      ⋃ (U : S.Etale) (σ : F.1.obj (op U)),
        U.hom.base '' (abelianSheafSectionSupport F U σ : Set U.left) := sorry

/-- An epimorphism of abelian sheaves gives the reverse inclusion of supports. -/
theorem abelianSheafSupport_subset_of_epi
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) [Epi φ] :
    abelianSheafSupport G ⊆ abelianSheafSupport F := sorry

/-- A monomorphism of abelian sheaves gives an inclusion of supports. -/
theorem abelianSheafSupport_subset_of_mono
    {F G : Sheaf S.smallEtaleTopology AddCommGrpCat.{u}} (φ : F ⟶ G) [Mono φ] :
    abelianSheafSupport F ⊆ abelianSheafSupport G := sorry

end AlgebraicGeometry.Scheme.Etale

end
