/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import ReasLib.Topology.Sheaves.Pullback.Composition
public import ReasLib.Topology.Spectral.CompactOpenIntersection
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of differences of directed compact-open intersections

All stage differences `U \ E` are modeled as opens of the single complement space `Eᶜ`.
Consequently, their transition maps are ordinary cohomology restriction maps for one fixed
coefficient sheaf.  The comparison target is the direct restriction of the original sheaf to
`W \ E`; pullback composition supplies the canonical coefficient comparison.
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology
open CategoryTheory.Limits

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology.CompactOpen.Difference

variable {X : TopCat.{u}}

/-- The restriction of `F` to the fixed complement subspace `Eᶜ`. -/
@[stacks 0A3D "coefficient sheaf on the fixed complement"]
abbrev complementSheaf (E : Set X) (F : X.Sheaf AddCommGrpCat.{u}) :
    (TopCat.subsetSpace Eᶜ).Sheaf AddCommGrpCat.{u} :=
  (TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.subsetInclusion Eᶜ)).obj F

/-- The cohomology diagram `U ↦ H^p(U \ E, F|_{Eᶜ})` on the opposite of a compact-open
family.  Every object is evaluated in the same complement space. -/
@[stacks 0A3D "compact-open difference cohomology diagram"]
abbrev diagram (S : Set (CompactOpens X)) (E : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) : Sᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (CompactOpenFamily.sdiffToOpens S E).toFunctor.op ⋙
    (complementSheaf E F).cohomologyPresheaf p

/-- Cohomology of the direct restriction of `F` to the subspace `W \ E`. -/
@[stacks 0A3D "compact-open difference cohomology target"]
abbrev target (W E : Set X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    AddCommGrpCat.{u} :=
  ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
    (TopCat.subsetInclusion (W \ E))).obj F).H' p
      (⊤ : Opens (TopCat.subsetSpace (W \ E)))

/-- Pulling `F` first to `Eᶜ` and then to `W \ E` agrees canonically with pulling it directly
to `W \ E`. -/
@[stacks 0A3D "composition of restrictions to a subset difference"]
noncomputable def coefficientIso (W E : Set X) (F : X.Sheaf AddCommGrpCat.{u}) :
    (TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.sdiffInclusion W E)).obj
        (complementSheaf E F) ≅
      (TopCat.Sheaf.pullback AddCommGrpCat.{u}
        (TopCat.subsetInclusion (W \ E))).obj F :=
  (TopCat.Sheaf.pullbackComp (A := AddCommGrpCat.{u})
      (TopCat.sdiffInclusion W E) (TopCat.subsetInclusion Eᶜ)).app F ≪≫
    eqToIso (congrArg
      (fun f ↦ (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).obj F)
      (TopCat.ext (fun _ ↦ rfl)))

/-- Transport from the inverse image of a stage open `U \ E` to the top open of `W \ E`,
before applying the coefficient comparison. -/
@[stacks 0A3D "compact-open difference inverse-image transport"]
noncomputable def preimageTopIso {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : S) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.sdiffInclusion W E)).obj (complementSheaf E F)).H' p
        ((Opens.map (TopCat.sdiffInclusion W E)).obj (U.1.sdiffOpen E)) ≅
      ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
        (TopCat.sdiffInclusion W E)).obj (complementSheaf E F)).H' p
          (⊤ : Opens (TopCat.subsetSpace (W \ E))) :=
  eqToIso (congrArg
    (fun V ↦ ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.sdiffInclusion W E)).obj (complementSheaf E F)).H' p V)
    (Opens.ext (Set.eq_univ_of_forall (fun x ↦
      Set.mem_iInter.mp
        (Set.mem_iInter.mp
          (Eq.mp (congrArg (fun T : Set X ↦ x.1 ∈ T) h.eq_iInter) x.property.1)
          U.1)
        U.property))))

/-- The canonical map from stage cohomology on `U \ E` to cohomology of the direct restriction
of `F` to `W \ E`. -/
@[stacks 0A3D "compact-open difference stage map"]
noncomputable def stageMap {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : S) :
    (diagram S E F p).obj (Opposite.op U) ⟶ target W E F p :=
  CategoryTheory.Sheaf.pullbackCohomologyMap
      (TopCat.sdiffInclusion W E) (complementSheaf E F) p (U.1.sdiffOpen E) ≫
    (preimageTopIso h E F p U).hom ≫
    CategoryTheory.Sheaf.cohomologyMap (coefficientIso W E F).hom p ⊤

/-- Restriction maps between stage differences commute with their canonical maps to
`(W \ E)`-cohomology. -/
@[stacks 0A3D "naturality of compact-open difference stage maps"]
theorem stageMap_naturality {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) {U V : Sᵒᵖ} (f : U ⟶ V) :
    (diagram S E F p).map f ≫ stageMap h E F p V.unop =
      stageMap h E F p U.unop := sorry

/-- The canonical cocone from compact-open difference cohomology to cohomology on `W \ E`. -/
@[stacks 0A3D "compact-open difference cohomology cocone"]
noncomputable def cocone {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) : Cocone (diagram S E F p) where
  pt := target W E F p
  ι :=
    { app U := stageMap h E F p U.unop
      naturality _ _ f := stageMap_naturality h E F p f }

/-- The canonical comparison from the colimit of stage-difference cohomology to cohomology on
`W \ E`. -/
@[stacks 0A3D "compact-open difference cohomology comparison"]
noncomputable def comparison {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    colimit (diagram S E F p) ⟶ target W E F p :=
  colimit.desc (diagram S E F p) (cocone h E F p)

/-- The compact-open difference comparison restricts at every stage to the canonical pullback,
top-open transport, and coefficient-comparison composite. -/
@[reassoc, stacks 0A3D "compact-open difference comparison at a stage"]
theorem ι_comp_comparison {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (E : Set X)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : Sᵒᵖ) :
    colimit.ι (diagram S E F p) U ≫ comparison h E F p =
      stageMap h E F p U.unop := sorry

/-- Lemma 20.22.1 (2) (0A3D): in a spectral space, removing a constructible subset from a
directed compact-open intersection commutes with cohomology after taking the filtered colimit
over the stage differences. -/
@[stacks 0A3D "cohomology of differences of a compact-open directed intersection"]
theorem comparison_isIso [SpectralSpace X]
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (hE : IsConstructible E)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (comparison h E F p) := sorry

end TopCat.Sheaf.Cohomology.CompactOpen.Difference
