/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SectionsSupportedIn

/-!
# Supported étale sections on containing opens

Sections supported on a locally closed subscheme are canonically identified
across open subschemes in which it is closed, by restriction to their intersection.
-/

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})
variable {Z : Scheme.{u}} (ι : Z ⟶ X)

/-- The image of `ι` is contained in the range of `U.ι` whenever it is contained
in the Zariski open `U`. -/
theorem range_subset_range_ι (U : X.Opens) (hU : Set.range ι ⊆ U) :
    Set.range ι ⊆ Set.range U.ι :=
  hU.trans (subset_of_eq U.range_ι.symm)

/-- A scheme morphism whose image lies in a Zariski open lifts through the
inclusion of that open. -/
def liftToOpen (U : X.Opens) (hU : Set.range ι ⊆ U) : Z ⟶ U :=
  IsOpenImmersion.lift U.ι ι (range_subset_range_ι ι U hU)

/-- The lift of `ι` through `U.ι` recovers `ι`. -/
theorem liftToOpen_fac (U : X.Opens) (hU : Set.range ι ⊆ U) :
    liftToOpen ι U hU ≫ U.ι = ι :=
  sorry

/-- If the image of `ι` is contained in Zariski opens `U` and `U'`, then it is
contained in `U ⊓ U'`. -/
theorem range_subset_inf (U U' : X.Opens) (hU : Set.range ι ⊆ U)
    (hU' : Set.range ι ⊆ U') : Set.range ι ⊆ (U ⊓ U' : X.Opens) :=
  Set.subset_inter hU hU'

/-- If `Z` is a closed subscheme of Zariski opens `U` and `U'`, then it is a
closed subscheme of `U ⊓ U'`. -/
instance isClosedImmersion_liftToOpen_inf {U U' : X.Opens}
    {hU : Set.range ι ⊆ U} {hU' : Set.range ι ⊆ U'}
    [IsClosedImmersion (liftToOpen ι U hU)]
    [IsClosedImmersion (liftToOpen ι U' hU')] :
    IsClosedImmersion (liftToOpen ι (U ⊓ U') (range_subset_inf ι U U' hU hU')) :=
  sorry

/-- The morphism in `X.Etale` associated to an inclusion of Zariski opens of
`X`. -/
abbrev openEtaleHom {U U' : X.Opens} (h : U' ≤ U) : mk U'.ι ⟶ mk U.ι :=
  MorphismProperty.Over.homMk (X.homOfLE h) (X.homOfLE_ι h)

/-- Restriction of supported sections from a Zariski open `U` to a smaller
Zariski open `U'` containing the image of `ι`. -/
def restrictSupportedInOpen (U U' : X.Opens) (hU : Set.range ι ⊆ U)
    (hU' : Set.range ι ⊆ U') (h : U' ≤ U) :
    abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU)) →+
      abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU')) where
  toFun σ := ⟨F.1.map (openEtaleHom h).op σ.val, sorry⟩
  map_zero' := sorry
  map_add' := sorry

/-- Restriction of supported sections on nested Zariski opens acts by the étale
sheaf restriction map. -/
theorem restrictSupportedInOpen_apply (U U' : X.Opens) (hU : Set.range ι ⊆ U)
    (hU' : Set.range ι ⊆ U') (h : U' ≤ U)
    (σ : abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU))) :
    (restrictSupportedInOpen F ι U U' hU hU' h σ).val =
      F.1.map (openEtaleHom h).op σ.val :=
  sorry

namespace SectionsSupportedInOpen

/-- The complement of a subscheme closed in `U` is open in the ambient scheme. -/
theorem complement_isOpen (U : X.Opens) (hU : Set.range ι ⊆ U)
    [IsClosedImmersion (liftToOpen ι U hU)] :
    IsOpen ((U : Set X) \ Set.range ι) := sorry

/-- The specified open complement of the support inside the larger open. -/
def complement (U : X.Opens) (hU : Set.range ι ⊆ U)
    [IsClosedImmersion (liftToOpen ι U hU)] : X.Opens :=
  ⟨(U : Set X) \ Set.range ι, complement_isOpen ι U hU⟩

/-- The complement open lies in `U`. -/
theorem complement_le (U : X.Opens) (hU : Set.range ι ⊆ U)
    [IsClosedImmersion (liftToOpen ι U hU)] : complement ι U hU ≤ U :=
  fun _ hx ↦ hx.1

variable (U U' : X.Opens) (hU : Set.range ι ⊆ U) (hU' : Set.range ι ⊆ U')
variable (h : U' ≤ U) [IsClosedImmersion (liftToOpen ι U hU)]

/-- The two pieces used for extension: the smaller open and the support complement. -/
def coverObj : Bool → X.Etale
  | false => mk U'.ι
  | true => mk (complement ι U hU).ι

/-- The two actual inclusions into the larger open. -/
def coverMap : (b : Bool) → coverObj ι U U' hU b ⟶ mk U.ι
  | false => openEtaleHom h
  | true => openEtaleHom (complement_le ι U hU)

/-- A containing smaller open and the complement of the closed support cover `U`. -/
theorem cover_mem (hU' : Set.range ι ⊆ U') :
    Sieve.ofArrows (coverObj ι U U' hU) (coverMap ι U U' hU h) ∈
      X.smallEtaleTopology (mk U.ι) := sorry

/-- The gluing datum is the supplied supported section on the smaller open and zero on
the complement, expressed as actual additive maps. -/
def family (b : Bool) :
    AddCommGrpCat.of
        (abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU'))) ⟶
      F.1.obj (op (coverObj ι U U' hU b)) :=
  match b with
  | false => AddCommGrpCat.ofHom
      (abelianSheafSectionsSupportedIn F (mk U'.ι)
        (Set.range (liftToOpen ι U' hU'))).subtype
  | true => 0

/-- Supported sections and zero agree after restriction to every overlap of the two pieces. -/
theorem family_compatible {W : X.Etale} {i j : Bool}
    (a : W ⟶ coverObj ι U U' hU i) (b : W ⟶ coverObj ι U U' hU j)
    (w : a ≫ coverMap ι U U' hU h i = b ≫ coverMap ι U U' hU h j) :
    family F ι U U' hU hU' i ≫ F.1.map a.op =
      family F ι U U' hU hU' j ≫ F.1.map b.op := sorry

/-- Sheaf amalgamation of the specified smaller-open/zero additive maps. -/
def amalgamate :
    AddCommGrpCat.of
        (abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU'))) ⟶
      F.1.obj (op (mk U.ι)) :=
  F.property.amalgamateOfArrows
    (coverMap ι U U' hU h) (cover_mem (ι := ι) (U := U) (U' := U') (hU := hU) (h := h) hU')
    (family F ι U U' hU hU')
    (fun {_} {_} {_} a b w ↦ family_compatible F ι U U' hU hU' h a b w)

/-- The amalgamation has support in the original closed subscheme. -/
theorem amalgamate_supported
    (σ : abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU'))) :
    amalgamate F ι U U' hU hU' h σ ∈
      abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU)) := sorry

end SectionsSupportedInOpen

/-- Extend a supported section by gluing it with zero on the open support complement. -/
def extendSupportedInOpen (U U' : X.Opens) (hU : Set.range ι ⊆ U)
    (hU' : Set.range ι ⊆ U') (h : U' ≤ U)
    [IsClosedImmersion (liftToOpen ι U hU)] :
    abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU')) →+
      abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU)) :=
  (SectionsSupportedInOpen.amalgamate F ι U U' hU hU' h).hom.codRestrict
    (abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU)))
    (SectionsSupportedInOpen.amalgamate_supported F ι U U' hU hU' h)

/-- Restriction recovers the smaller-open section from its zero extension. -/
theorem restrict_extendSupportedInOpen (U U' : X.Opens) (hU : Set.range ι ⊆ U)
    (hU' : Set.range ι ⊆ U') (h : U' ≤ U)
    [IsClosedImmersion (liftToOpen ι U hU)]
    (σ : abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU'))) :
    restrictSupportedInOpen F ι U U' hU hU' h
      (extendSupportedInOpen F ι U U' hU hU' h σ) = σ := sorry

/-- A supported section on the larger open is the zero extension of its restriction. -/
theorem extend_restrictSupportedInOpen (U U' : X.Opens) (hU : Set.range ι ⊆ U)
    (hU' : Set.range ι ⊆ U') (h : U' ≤ U)
    [IsClosedImmersion (liftToOpen ι U hU)]
    (σ : abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU))) :
    extendSupportedInOpen F ι U U' hU hU' h
      (restrictSupportedInOpen F ι U U' hU hU' h σ) = σ := sorry

/-- Restriction to a containing smaller open has the specified zero-extension inverse. -/
def restrictSupportedInOpenAddEquiv (U U' : X.Opens) (hU : Set.range ι ⊆ U)
    (hU' : Set.range ι ⊆ U') (h : U' ≤ U)
    [IsClosedImmersion (liftToOpen ι U hU)] :
    abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU)) ≃+
      abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU')) where
  toFun := restrictSupportedInOpen F ι U U' hU hU' h
  invFun := extendSupportedInOpen F ι U U' hU hU' h
  left_inv := extend_restrictSupportedInOpen F ι U U' hU hU' h
  right_inv := restrict_extendSupportedInOpen F ι U U' hU hU' h
  map_add' := (restrictSupportedInOpen F ι U U' hU hU' h).map_add

/-- For an abelian étale sheaf and a locally closed subscheme, two containing
Zariski opens on which the subscheme is closed have canonically additively
equivalent groups of sections supported on the subscheme. -/
def abelianSheafSectionsSupportedInOpenAddEquiv (U U' : X.Opens)
    (hU : Set.range ι ⊆ U) (hU' : Set.range ι ⊆ U') [IsImmersion ι]
    [IsClosedImmersion (liftToOpen ι U hU)]
    [IsClosedImmersion (liftToOpen ι U' hU')] :
    abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU)) ≃+
      abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU')) :=
  (restrictSupportedInOpenAddEquiv F ι U (U ⊓ U') hU
      (range_subset_inf ι U U' hU hU') inf_le_left).trans
    (restrictSupportedInOpenAddEquiv F ι U' (U ⊓ U') hU'
      (range_subset_inf ι U U' hU hU') inf_le_right).symm

/-- If `U' ≤ U`, the canonical comparison of supported sections is restriction
along the inclusion of Zariski opens. -/
theorem abelianSheafSectionsSupportedInOpenAddEquiv_apply_of_le (U U' : X.Opens)
    (hU : Set.range ι ⊆ U) (hU' : Set.range ι ⊆ U') [IsImmersion ι]
    [IsClosedImmersion (liftToOpen ι U hU)]
    [IsClosedImmersion (liftToOpen ι U' hU')] (h_le : U' ≤ U)
    (σ : abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU))) :
    (abelianSheafSectionsSupportedInOpenAddEquiv F ι U U' hU hU' σ).val =
      F.1.map (openEtaleHom h_le).op σ.val :=
  sorry

end AlgebraicGeometry.Scheme.Etale

end
