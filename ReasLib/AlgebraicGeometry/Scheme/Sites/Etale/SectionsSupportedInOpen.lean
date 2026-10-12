/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
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

/-- For an abelian étale sheaf and a locally closed subscheme, two containing
Zariski opens on which the subscheme is closed have canonically additively
equivalent groups of sections supported on the subscheme. -/
def abelianSheafSectionsSupportedInOpenAddEquiv (U U' : X.Opens)
    (hU : Set.range ι ⊆ U) (hU' : Set.range ι ⊆ U') [IsImmersion ι]
    [IsClosedImmersion (liftToOpen ι U hU)]
    [IsClosedImmersion (liftToOpen ι U' hU')] :
    abelianSheafSectionsSupportedIn F (mk U.ι) (Set.range (liftToOpen ι U hU)) ≃+
      abelianSheafSectionsSupportedIn F (mk U'.ι) (Set.range (liftToOpen ι U' hU')) :=
  (AddEquiv.ofBijective
      (restrictSupportedInOpen F ι U (U ⊓ U') hU
        (range_subset_inf ι U U' hU hU') inf_le_left) sorry).trans
    (AddEquiv.ofBijective
      (restrictSupportedInOpen F ι U' (U ⊓ U') hU'
        (range_subset_inf ι U U' hU hU') inf_le_right) sorry).symm

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
