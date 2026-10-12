/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Spectral.Basic
public import Mathlib.Topology.Spectral.Hom
public import ReasLib.CategoryTheory.Sites.AbelianSheaf.Grothendieck
public import ReasLib.Topology.Category.TopCat.Subset
public import ReasLib.Topology.Sheaf.Cohomology.Pushforward
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology over the inverse image of a specializing locus

For a continuous map `f : X ⟶ Y` and `y : Y`, this leaf owns the canonical comparison from
the filtered colimit of `H^p(f⁻¹U, F)` over open neighbourhoods `U` of `y` to the cohomology
of `F` restricted to `f⁻¹(nhdsKer {y})`.

The comparison exists without spectral hypotheses. Spectrality is used only to prove that it is
an isomorphism.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace TopCat.Sheaf.Cohomology.SpecializingPreimage

variable {X Y : TopCat.{u}}

/-- The inverse image of the set of points specializing to `y`. -/
@[stacks 0A3E "inverse image of a specializing locus"]
abbrev locus (f : X ⟶ Y) (y : Y) : Set X :=
  f ⁻¹' nhdsKer ({y} : Set Y)

/-- The cohomology diagram `U ↦ H^p(f⁻¹U, F)` on open neighbourhoods of `y`. -/
@[stacks 0A3E "cohomology diagram over neighbourhoods of a point"]
abbrev diagram (f : X ⟶ Y) (y : Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    (OpenNhds y)ᵒᵖ ⥤ AddCommGrpCat.{u} :=
  (OpenNhds.inclusion y).op ⋙
    (TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).obj (F.cohomologyPresheaf p)

/-- Cohomology of the restriction of `F` to the inverse image of the specializing locus of `y`. -/
@[stacks 0A3E "cohomology on an inverse-image specializing locus"]
abbrev target (f : X ⟶ Y) (y : Y) (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    AddCommGrpCat.{u} :=
  ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
    (TopCat.subsetInclusion (locus f y))).obj F).H' p
      (⊤ : Opens (TopCat.subsetSpace (locus f y)))

/-- Pulling a neighbourhood of `y` back to `f⁻¹(nhdsKer {y})` gives the top open. -/
@[stacks 0A3E "neighbourhood pullback to an inverse-image specializing locus"]
theorem preimageTop (f : X ⟶ Y) (y : Y) (U : OpenNhds y) :
    (Opens.map (TopCat.subsetInclusion (locus f y))).obj
        ((Opens.map f).obj U.1) =
      (⊤ : Opens (TopCat.subsetSpace (locus f y))) := sorry

/-- Transport cohomology on the inverse image of a neighbourhood to the top open of the
specializing subspace. -/
@[stacks 0A3E "cohomology transport to an inverse-image specializing locus"]
noncomputable def preimageTopIso (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : OpenNhds y) :
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.subsetInclusion (locus f y))).obj F).H' p
        ((Opens.map (TopCat.subsetInclusion (locus f y))).obj
          ((Opens.map f).obj U.1)) ≅
      target f y F p :=
  eqToIso (congrArg
    (fun V ↦ ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.subsetInclusion (locus f y))).obj F).H' p V)
    (preimageTop f y U))

/-- The canonical map from `H^p(f⁻¹U, F)` to cohomology on
`f⁻¹(nhdsKer {y})`. -/
@[stacks 0A3E "neighbourhood stage map to specializing-locus cohomology"]
noncomputable def stageMap (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : OpenNhds y) :
    (diagram f y F p).obj (Opposite.op U) ⟶ target f y F p :=
  CategoryTheory.Sheaf.pullbackCohomologyMap
      (TopCat.subsetInclusion (locus f y)) F p ((Opens.map f).obj U.1) ≫
    (preimageTopIso f y F p U).hom

/-- Restriction between neighbourhoods commutes with their canonical maps to
specializing-locus cohomology. -/
@[stacks 0A3E "naturality of specializing-preimage stage maps"]
theorem stageMap_naturality (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ)
    {U V : (OpenNhds y)ᵒᵖ} (i : U ⟶ V) :
    (diagram f y F p).map i ≫ stageMap f y F p V.unop =
      stageMap f y F p U.unop := sorry

/-- The canonical cocone from neighbourhood cohomology to cohomology on the inverse-image
specializing locus. -/
@[stacks 0A3E "specializing-preimage cohomology cocone"]
noncomputable def cocone (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    Cocone (diagram f y F p) where
  pt := target f y F p
  ι :=
    { app U := stageMap f y F p U.unop
      naturality _ _ i := stageMap_naturality f y F p i }

/-- The canonical comparison from the colimit of `H^p(f⁻¹U, F)` to cohomology on
`f⁻¹(nhdsKer {y})`. -/
@[stacks 0A3E "neighbourhood-colimit comparison for a specializing preimage"]
noncomputable def comparison (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    colimit (diagram f y F p) ⟶ target f y F p :=
  colimit.desc (diagram f y F p) (cocone f y F p)

/-- The specializing-preimage comparison restricts at each neighbourhood to the canonical
pullback map on cohomology. -/
@[reassoc, stacks 0A3E "specializing-preimage comparison at a neighbourhood"]
theorem ι_comp_comparison (f : X ⟶ Y) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) (U : (OpenNhds y)ᵒᵖ) :
    colimit.ι (diagram f y F p) U ≫ comparison f y F p =
      stageMap f y F p U.unop := sorry

/-- The morphism of neighbourhood cohomology diagrams induced by a morphism of coefficient
sheaves. -/
@[stacks 0A3E "coefficient map on the specializing-preimage diagram"]
abbrev diagramMap (f : X ⟶ Y) (y : Y) {F G : X.Sheaf AddCommGrpCat.{u}}
    (a : F ⟶ G) (p : ℕ) :
    diagram f y F p ⟶ diagram f y G p :=
  Functor.whiskerLeft (OpenNhds.inclusion y).op
    ((TopCat.Presheaf.pushforward AddCommGrpCat.{u} f).map
      ((CategoryTheory.Sheaf.cohomologyPresheafFunctor
        (Opens.grothendieckTopology X) p).map a))

/-- The morphism on specializing-locus cohomology induced by a morphism of coefficient sheaves. -/
@[stacks 0A3E "coefficient map on specializing-preimage cohomology"]
abbrev targetMap (f : X ⟶ Y) (y : Y) {F G : X.Sheaf AddCommGrpCat.{u}}
    (a : F ⟶ G) (p : ℕ) :
    target f y F p ⟶ target f y G p :=
  CategoryTheory.Sheaf.cohomologyMap
    ((TopCat.Sheaf.pullback AddCommGrpCat.{u}
      (TopCat.subsetInclusion (locus f y))).map a) p
    (⊤ : Opens (TopCat.subsetSpace (locus f y)))

/-- The canonical map from a neighbourhood stage is natural in the coefficient sheaf. -/
@[reassoc, stacks 0A3E "coefficient naturality of specializing-preimage stage maps"]
theorem stageMap_map (f : X ⟶ Y) (y : Y)
    {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (p : ℕ) (U : OpenNhds y) :
    (diagramMap f y a p).app (Opposite.op U) ≫ stageMap f y G p U =
      stageMap f y F p U ≫ targetMap f y a p := sorry

/-- The colimit comparison is natural in the coefficient sheaf. -/
@[stacks 0A3E "coefficient naturality of the specializing-preimage comparison"]
theorem comparison_map (f : X ⟶ Y) (y : Y)
    {F G : X.Sheaf AddCommGrpCat.{u}} (a : F ⟶ G) (p : ℕ) :
    colim.map (diagramMap f y a p) ≫ comparison f y G p =
      comparison f y F p ≫ targetMap f y a p := sorry

/-- Lemma 20.22.2 (0A3E), neighbourhood-colimit form: for a spectral map from a spectral
space to a prespectral space, the canonical comparison to cohomology on the inverse image of a
point's specializing locus is an isomorphism. -/
@[stacks 0A3E "cohomology on the inverse image of a specializing locus"]
theorem comparison_isIso [SpectralSpace X] [PrespectralSpace Y]
    (f : X ⟶ Y) (hf : IsSpectralMap f) (y : Y)
    (F : X.Sheaf AddCommGrpCat.{u}) (p : ℕ) :
    IsIso (comparison f y F p) := sorry

end TopCat.Sheaf.Cohomology.SpecializingPreimage

/- Audit the explicit comparison data. -/
