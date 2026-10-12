/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Spectral.Basic
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Category.TopCat.Subset
public import ReasLib.Topology.CompactOpen.Intersection
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of directed intersections of compact opens

This leaf owns the canonical comparison from the filtered colimit of cohomology on a
downward-directed family of compact opens to cohomology on its intersection.  The presentation
of the intersection is supplied by `IsCompactOpenDirectedIntersection`; spectrality is needed
only for invertibility of the comparison.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology.CompactOpen.Intersection

variable {X : TopCat.{u}}

/-- The cohomology diagram `U ↦ H^p(U, F)` on the opposite of a family of compact opens. -/
@[stacks 0A3D "compact-open intersection cohomology diagram"]
abbrev diagram (S : Set (CompactOpens X)) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    Sᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (compactOpenFamilyToOpens S).toFunctor.op ⋙ F.cohomologyPresheaf p

/-- Cohomology of the pullback of `F` to the subspace carried by `W`. -/
@[stacks 0A3D "compact-open intersection cohomology target"]
abbrev target (W : Set X) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    AddCommGrpCat.{u} :=
  ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.subsetInclusion W)).obj F).H' p
    (⊤ : Opens (TopCat.subsetSpace W))

/-- Transport cohomology on the inverse image of a displayed compact open to cohomology on the
top open of the intersection subspace. -/
@[stacks 0A3D "compact-open intersection inverse-image transport"]
noncomputable def preimageTopIso {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) (U : S) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u} (TopCat.subsetInclusion W)).obj F).H' p
        ((Opens.map (TopCat.subsetInclusion W)).obj U.1.toOpens) ≅
      target W F p :=
  eqToIso (congrArg
    (fun V ↦ ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.subsetInclusion W)).obj F).H' p V)
    (Opens.ext (Set.eq_univ_of_forall (fun x ↦
      Set.mem_iInter.mp
        (Set.mem_iInter.mp
          (Eq.mp (congrArg (fun T : Set X ↦ x.1 ∈ T) h.eq_iInter) x.property) U.1)
        U.property))))

/-- The canonical pullback map from cohomology on a displayed compact open to cohomology on
the intersection subspace. -/
@[stacks 0A3D "compact-open intersection stage map"]
noncomputable def stageMap {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) (U : S) :
    (diagram S F p).obj (Opposite.op U) ⟶ target W F p :=
  CategoryTheory.Sheaf.pullbackCohomologyMap
      (TopCat.subsetInclusion W) F p U.1.toOpens ≫
    (preimageTopIso h F p U).hom

/-- Restriction maps between displayed compact opens commute with their canonical maps to
intersection-subspace cohomology. -/
@[stacks 0A3D "naturality of compact-open intersection stage maps"]
theorem stageMap_naturality {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) {U V : Sᵒᵖ} (f : U ⟶ V) :
    (diagram S F p).map f ≫ stageMap h F p V.unop =
      stageMap h F p U.unop := sorry

/-- The canonical cocone from compact-open stage cohomology to cohomology on the intersection
subspace. -/
@[stacks 0A3D "compact-open intersection cohomology cocone"]
noncomputable def cocone {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) :
    Cocone (diagram S F p) where
  pt := target W F p
  ι :=
    { app U := stageMap h F p U.unop
      naturality _ _ f := stageMap_naturality h F p f }

/-- The canonical map from the colimit of compact-open stage cohomology to cohomology on the
intersection subspace. -/
@[stacks 0A3D "compact-open intersection cohomology comparison"]
noncomputable def comparison {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) :
    colimit (diagram S F p) ⟶ target W F p :=
  colimit.desc (diagram S F p) (cocone h F p)

/-- The compact-open intersection comparison restricts at every stage to the canonical pullback
map on cohomology. -/
@[reassoc, stacks 0A3D "compact-open intersection comparison at a stage"]
theorem ι_comp_comparison {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) (U : Sᵒᵖ) :
    colimit.ι (diagram S F p) U ≫ comparison h F p =
      stageMap h F p U.unop := sorry

/-- Lemma 20.22.1 (0A3D): in a spectral space, the canonical map from the colimit of
cohomology over a directed compact-open presentation to cohomology on its intersection is an
isomorphism in every degree. -/
@[stacks 0A3D "cohomology of a compact-open directed intersection"]
theorem comparison_isIso [SpectralSpace X]
    {W : Set X} {S : Set (CompactOpens X)}
    (h : IsCompactOpenDirectedIntersection W S) (F : X.Sheaf AddCommGrpCat.{u})
    (p : ℕ) :
    IsIso (comparison h F p) := sorry

end TopCat.Sheaf.Cohomology.CompactOpen.Intersection
