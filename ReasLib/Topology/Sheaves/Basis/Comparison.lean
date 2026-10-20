module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
public import ReasLib.Topology.Sheaves.Basis.Neighborhoods
public import ReasLib.Topology.Sheaves.Basis.SheafCondition

/-!
# Comparison of sheaves on a basis with sheaves on the ambient space

This file exposes the dense-subsite equivalence, its extension and restriction functors, and the
induced comparison of stalks.
-/

@[expose] public section

open CategoryTheory Limits Opposite TopologicalSpace TopCat TopCat.Presheaf Functor.Final

noncomputable section

universe u v w

set_option backward.isDefEq.respectTransparency false

section Comparison

variable {X : TopCat.{w}}
variable {C : Type u} [Category.{v} C]
variable {B : Set (Opens X)}

namespace BasisSheaf

/-- The source basis-cover sheaf category and the canonical category of sheaves for the induced
Grothendieck topology have the same objects and morphisms. -/
public noncomputable def basisSheafEquivBasisSiteSheaf (hB : Opens.IsBasis B) :
    BasisSheaf.{w, v} B ≌ BasisSiteSheaf (Type v) B :=
  ObjectProperty.fullSubcategoryCongr
    (funext fun F ↦ propext (CategoryTheory.Presheaf.isBasisSheaf_iff_isSheaf hB F))

end BasisSheaf

namespace BasisSiteSheaf

variable {hB : Opens.IsBasis B}

/-- The underlying presheaf of a sheaf on the basis `B`. -/
abbrev presheaf (F : BasisSiteSheaf C B) : (BasisOpen B)ᵒᵖ ⥤ C :=
  F.1

/-- Size-indexed completeness supplies the structured-arrow limits used by extension from a
topological basis. -/
instance instHasLimitsOfShapeStructuredArrow
    (B : Set (Opens X)) [HasLimitsOfSize.{w, w} C] :
    ∀ U : (Opens X)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C :=
  fun _ ↦ HasLimitsOfSize.has_limits_of_shape
    (C := C) (StructuredArrow _ (basisOpenInclusion B).op)

variable [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C]

/-- The dense-subsite equivalence between sheaves on the induced basis-open site and sheaves on
`X`. -/
public noncomputable abbrev basisSiteSheafComparisonEquiv (hB : Opens.IsBasis B) :
    BasisSiteSheaf C B ≌ TopCat.Sheaf C X :=
  -- Local instance justification (defeq pin): the upstream dense-subsite equivalence requires the cover-density class determined by the explicit basis proof; do not register a global instance.
  letI : (basisOpenInclusion B).IsCoverDense (Opens.grothendieckTopology X) :=
    basisOpenInclusion_isCoverDense hB
  (basisOpenInclusion B).sheafInducedTopologyEquivOfIsCoverDense
    (Opens.grothendieckTopology X) C

/-- The canonical functor extending sheaves from the basis `B` to all opens of `X`. -/
public noncomputable abbrev extendFunctor (hB : Opens.IsBasis B) :
    BasisSiteSheaf C B ⥤ TopCat.Sheaf C X :=
  (basisSiteSheafComparisonEquiv (C := C) hB).functor

/-- The canonical functor restricting sheaves on `X` to the basis site attached to `B`. -/
public noncomputable abbrev restrictFunctor (hB : Opens.IsBasis B) :
    TopCat.Sheaf C X ⥤ BasisSiteSheaf C B :=
  (basisSiteSheafComparisonEquiv (C := C) hB).inverse

/-- The sheaf on `X` obtained by extending a sheaf on the basis `B` along the dense inclusion of
basis opens into all opens. -/
abbrev extend (F : BasisSiteSheaf C B) (hB : Opens.IsBasis B) : TopCat.Sheaf C X :=
  (extendFunctor (C := C) hB).obj F

/-- The sheaf on the basis site obtained by restricting a sheaf on `X` to basis opens. -/
abbrev restrict (hB : Opens.IsBasis B) (F : TopCat.Sheaf C X) : BasisSiteSheaf C B :=
  (restrictFunctor (C := C) hB).obj F

/-- The unit comparison identifies a basis sheaf with the restriction of its extension. -/
public noncomputable def restrictExtendSheafIso (F : BasisSiteSheaf C B)
    (hB : Opens.IsBasis B) :
    F ≅ restrict hB (F.extend hB) :=
  (basisSiteSheafComparisonEquiv (C := C) hB).unitIso.app F

/-- The counit comparison identifies extension after basis restriction with the original sheaf. -/
public noncomputable def extendRestrictSheafIso (F : TopCat.Sheaf C X)
    (hB : Opens.IsBasis B) :
    (restrict hB F).extend hB ≅ F :=
  (basisSiteSheafComparisonEquiv (C := C) hB).counitIso.app F

/-- The presheaf underlying basis restriction is precomposition with the basis inclusion. -/
theorem restrict_presheaf (hB : Opens.IsBasis B) (F : TopCat.Sheaf C X) :
    (restrict hB F).presheaf = (basisOpenInclusion B).op ⋙ F.presheaf := sorry

/-- The presheaf-level unit comparison obtained by forgetting the sheaf condition from the
canonical dense-subsite unit.  This is the single owner of the restriction comparison; the
component accessors below are only convenience projections for section-level arguments. -/
abbrev restrictExtendIso (F : BasisSiteSheaf C B) (hB : Opens.IsBasis B) :
    F.presheaf ≅ (basisOpenInclusion B).op ⋙ (F.extend hB).presheaf :=
  (sheafToPresheaf (basisGrothendieckTopology B) C).mapIso
    (F.restrictExtendSheafIso hB)

/-- An isomorphism after restriction to a topological basis determines an isomorphism of the
ambient sheaves. -/
public noncomputable def isoOfRestrictIso
    (hB : Opens.IsBasis B) {F G : TopCat.Sheaf C X}
    (e : restrict hB F ≅ restrict hB G) :
    F ≅ G :=
  (extendRestrictSheafIso F hB).symm ≪≫
    (extendFunctor (C := C) hB).mapIso e ≪≫
    extendRestrictSheafIso G hB

/-- The diagram of sections of a basis sheaf over basis opens containing `x`. -/
abbrev stalkDiagram (F : BasisSiteSheaf C B) (x : X) :
    (BasisOpenNhds B x)ᵒᵖ ⥤ C :=
  (basisOpenNhdsInclusion B x).op ⋙ F.presheaf

/-- The diagram obtained by evaluating the extended sheaf `F.extend hB` on basis neighborhoods of
`x`. -/
abbrev extendStalkDiagram (F : BasisSiteSheaf C B) (hB : Opens.IsBasis B) (x : X) :
    (BasisOpenNhds B x)ᵒᵖ ⥤ C :=
  (basisOpenNhdsToOpenNhds B x).op ⋙ (OpenNhds.inclusion x).op ⋙ (F.extend hB).presheaf

/-- The component over a basis open of the canonical restriction comparison from `F` to the
restriction of `F.extend hB` back to the basis. -/
abbrev restrictExtendComponentHom (F : BasisSiteSheaf C B) (hB : Opens.IsBasis B)
    (U : (BasisOpen B)ᵒᵖ) :
    F.presheaf.obj U ⟶ ((basisOpenInclusion B).op ⋙ (F.extend hB).presheaf).obj U :=
  (F.restrictExtendIso hB).hom.app U

/-- The component over a basis open of the inverse restriction comparison from `F.extend hB` back to
`F`. -/
abbrev restrictExtendComponentInv (F : BasisSiteSheaf C B) (hB : Opens.IsBasis B)
    (U : (BasisOpen B)ᵒᵖ) :
    ((basisOpenInclusion B).op ⋙ (F.extend hB).presheaf).obj U ⟶ F.presheaf.obj U :=
  (F.restrictExtendIso hB).inv.app U

-- Proof sketch: this is the componentwise naturality of the unit transformation of the
-- dense-subsite comparison equivalence, rewritten using the explicit description of `F.extend` on
-- basis opens.
/-- The restriction comparison from `F` to `F.extend` is natural in the basis open. -/
theorem restrictExtendHom_naturality (F : BasisSiteSheaf C B)
    (hB : Opens.IsBasis B)
    {U V : (BasisOpen B)ᵒᵖ}
    (i : U ⟶ V) :
    F.presheaf.map i ≫ F.restrictExtendComponentHom hB V =
      F.restrictExtendComponentHom hB U ≫
        ((basisOpenInclusion B).op ⋙ (F.extend hB).presheaf).map i := sorry

-- Proof sketch: this is the componentwise naturality of the inverse of the unit transformation of
-- the dense-subsite comparison equivalence.
/-- The inverse restriction comparison from `F.extend` back to `F` is natural in the basis open. -/
theorem restrictExtendInv_naturality (F : BasisSiteSheaf C B)
    (hB : Opens.IsBasis B)
    {U V : (BasisOpen B)ᵒᵖ}
    (i : U ⟶ V) :
    ((basisOpenInclusion B).op ⋙ (F.extend hB).presheaf).map i ≫
        F.restrictExtendComponentInv hB V =
      F.restrictExtendComponentInv hB U ≫ F.presheaf.map i := sorry

-- Proof sketch: these are the componentwise inverse identities of the unit isomorphism of the
-- dense-subsite comparison equivalence.
/-- On each basis open, the forward and inverse restriction comparison maps compose to the
identity on `F`. -/
theorem restrictExtend_component_hom_inv_id (F : BasisSiteSheaf C B)
    (hB : Opens.IsBasis B)
    (U : (BasisOpen B)ᵒᵖ) :
    F.restrictExtendComponentHom hB U ≫ F.restrictExtendComponentInv hB U =
      𝟙 (F.presheaf.obj U) := sorry

-- Proof sketch: these are the componentwise inverse identities of the unit isomorphism of the
-- dense-subsite comparison equivalence.
/-- On each basis open, the inverse and forward restriction comparison maps compose to the identity
on the restriction of `F.extend`. -/
theorem restrictExtend_component_inv_hom_id (F : BasisSiteSheaf C B)
    (hB : Opens.IsBasis B)
    (U : (BasisOpen B)ᵒᵖ) :
    F.restrictExtendComponentInv hB U ≫ F.restrictExtendComponentHom hB U =
      𝟙 (((basisOpenInclusion B).op ⋙ (F.extend hB).presheaf).obj U) := sorry

/-- The basis stalk diagram of `F` is canonically isomorphic to the basis-neighborhood diagram
obtained from `F.extend`. -/
public noncomputable def stalkDiagramIso (F : BasisSiteSheaf C B)
    (hB : Opens.IsBasis B) (x : X) :
    F.stalkDiagram x ≅ F.extendStalkDiagram hB x :=
  Functor.isoWhiskerLeft (basisOpenNhdsInclusion B x).op (F.restrictExtendIso hB) ≪≫
    Functor.isoWhiskerRight (basisOpenNhdsInclusionIso B x) (F.extend hB).presheaf

end BasisSiteSheaf

namespace BasisSheaf

variable [∀ U : (Opens X)ᵒᵖ,
  HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) (Type v)]

/-- The canonical comparison equivalence between source-style sheaves on a topological basis and
sheaves on the whole space. -/
public noncomputable def basisSheafComparisonEquiv (hB : Opens.IsBasis B) :
    BasisSheaf.{w, v} B ≌ TopCat.Sheaf (Type v) X :=
  (basisSheafEquivBasisSiteSheaf hB).trans
    (BasisSiteSheaf.basisSiteSheafComparisonEquiv (C := Type v) hB)

/-- The canonical extension to all opens of a source-style sheaf on a topological basis. -/
noncomputable abbrev extend (F : BasisSheaf.{w, v} B) (hB : Opens.IsBasis B) :
    TopCat.Sheaf (Type v) X :=
  (basisSheafComparisonEquiv hB).functor.obj F

end BasisSheaf

end Comparison

section Stalks

variable {X : TopCat.{v}}
variable {C : Type u} [Category.{v} C]
variable {B : Set (Opens X)}
variable {hB : Opens.IsBasis B}
variable [∀ U : (Opens X)ᵒᵖ, HasLimitsOfShape (StructuredArrow U (basisOpenInclusion B).op) C]
variable [HasColimits C]

namespace BasisSiteSheaf

/-- The stalk of a sheaf on the basis `B` at `x`, computed as the colimit over basis
neighborhoods of `x`. -/
abbrev stalk (F : BasisSiteSheaf C B) (x : X) : C :=
  colimit (F.stalkDiagram x)

/-- The canonical comparison isomorphism from the basis stalk of `F` at `x` to the stalk at `x`
of its extension to all opens. -/
noncomputable def stalkComparisonIso (F : BasisSiteSheaf C B) (hB : Opens.IsBasis B) (x : X) :
    F.stalk x ≅ Presheaf.stalk (F.extend hB).presheaf x :=
  -- Local instance justification (defeq pin): `colimitIso` requires the finality class canonically determined by `hB` and `x`.
  letI : Functor.Final (basisOpenNhdsToOpenNhds B x).op :=
    basisOpenNhdsToOpenNhds_final hB x
  let G := (F.extend hB).presheaf
  (HasColimit.isoOfNatIso (F.stalkDiagramIso hB x)) ≪≫
    colimitIso (basisOpenNhdsToOpenNhds B x).op ((OpenNhds.inclusion x).op ⋙ G)

/-- The forward map of `stalkComparisonIso`. -/
abbrev stalkComparison (F : BasisSiteSheaf C B) (hB : Opens.IsBasis B) (x : X) :
    F.stalk x ⟶ Presheaf.stalk (F.extend hB).presheaf x :=
  (F.stalkComparisonIso hB x).hom

/-- The basis-stalk comparison carries the colimit injection of a basis neighborhood to the germ
of the corresponding section of the extended sheaf. -/
theorem stalkComparison_ι (F : BasisSiteSheaf C B)
    (hB : Opens.IsBasis B) (W : BasisOpen B) (y : W.1) :
    colimit.ι (F.stalkDiagram y.1) (op ⟨W, y.2⟩) ≫ F.stalkComparison hB y.1 =
      F.restrictExtendComponentHom hB (op W) ≫
        (F.extend hB).presheaf.germ W.1 y.1 y.2 := sorry

end BasisSiteSheaf

namespace BasisSiteSheaf

-- Proof sketch: the unit isomorphism of the dense-subsite comparison identifies `F` with the
-- restriction of `F.extend` to basis opens, giving a comparison between the two basis-neighborhood
-- diagrams. Since basis neighborhoods are final in all neighborhoods of `x`, the induced colimit
-- map from `F.stalk x` to `F.extend.presheaf.stalk x` is an isomorphism.
/-- Basis extension preserves stalks: the canonical comparison morphism from the basis stalk `F_x`
to the stalk of the extended sheaf `F_x^{ext}` is an isomorphism. -/
theorem stalkComparison_isIso (F : BasisSiteSheaf C B)
    (hB : Opens.IsBasis B) (x : X) :
    IsIso (stalkComparison F hB x) := sorry

end BasisSiteSheaf

end Stalks
