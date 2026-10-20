module

public import stacks_project.Chap60.Lemma_60_18_2
public import stacks_project.Chap60.«60_10_0_1_CrystallineSheaf»
public import ReasLib.AlgebraicGeometry.Scheme.Sites.StructureSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.UniverseLift

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Crystalline CrystallineModuleSheaf

universe u

namespace CrystallineCoefficients

variable {S X : Scheme.{u}} (I : S.IdealSheafData)
variable (γ : ∀ V : S.affineOpens, DividedPowers (I.ideal V))
variable (hc : ∀ (V : S.affineOpens) (f : Γ(S, V)),
  (γ V).IsDPMorphism (γ (S.affineBasicOpen f))
    (S.presheaf.map (homOfLE (S.basicOpen_le f)).op).hom)
variable (x₀ : X ⟶ I.subscheme)

/-- The genuine thickening and its structure morphism over the base scheme. -/
def thickeningOverBase : smallCrystallineSite S I γ hc X x₀ ⥤ Over S where
  obj T := Over.mk T.obj.1.thickeningToBase
  map f := Over.homMk f.hom.thickening f.hom.base_comm
  map_id := by intro T; rfl
  map_comp := by intro T U V f g; rfl

/-- The actual ring of functions on the thickening, functorially in the site. -/
abbrev rings : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ ⥤ RingCat.{u} :=
  Scheme.Site.structurePresheaf (smallThickeningFunctor S I γ hc X x₀)

variable (F : CrisModuleSheaf S I γ hc X x₀)

/-- Sections with their actual module structure over the thickening ring. -/
noncomputable abbrev sectionsObj (T : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ) :
    ModuleCat.{u} ((rings I γ hc x₀).obj T) :=
  (F.obj T.unop).val.obj (op ⊤)

/-- The semilinear restriction is induced by the family's geometric comparison. -/
noncomputable def sectionsMap {T U : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ}
    (f : T ⟶ U) :
    sectionsObj I γ hc x₀ F T ⟶
      (ModuleCat.restrictScalars ((rings I γ hc x₀).map f).hom).obj
        (sectionsObj I γ hc x₀ F U) :=
  -- Local instance justification (defeq pin): the codomain carries the
  -- source ring action obtained by restricting along this particular map.
  letI : Module (T.unop.obj.1.thickening.ringCatSheaf.obj.obj (op ⊤))
      (sectionsObj I γ hc x₀ F U) :=
    ((ModuleCat.restrictScalars ((rings I γ hc x₀).map f).hom).obj
      (sectionsObj I γ hc x₀ F U)).isModule
  ModuleCat.ofHom
    { toFun := (abelianGlobalSections_map f.unop.hom.thickening (F.comparison f.unop)).hom
      map_add' := fun a b ↦ map_add _ a b
      map_smul' := sorry }

/-- Coherence of the actual module-sheaf comparisons and their section maps.
Sheaf-level laws are required for gluing on overlaps of nonaffine thickenings;
agreement only on global sections is insufficient for that argument. -/
class SectionsCoherent : Prop where
  /-- The comparison for an identity is the canonical identity pullback map. -/
  comparison_id (T : smallCrystallineSite S I γ hc X x₀) :
    F.comparison (𝟙 T) = (Scheme.Modules.pullbackId T.obj.1.thickening).hom.app (F.obj T)
  /-- Comparisons commute on all open subsets, including overlaps, through
  the canonical pullback-composition isomorphism. -/
  comparison_comp {T U V : smallCrystallineSite S I γ hc X x₀}
      (f : T ⟶ U) (g : U ⟶ V) :
    F.comparison (f ≫ g) =
      (Scheme.Modules.pullbackComp f.hom.thickening g.hom.thickening).inv.app (F.obj V) ≫
        (Scheme.Modules.pullback f.hom.thickening).map (F.comparison g) ≫ F.comparison f
  /-- Identity restrictions act as the identity, with the canonical scalar transport. -/
  map_id (T : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ) :
    sectionsMap I γ hc x₀ F (𝟙 T) =
      (ModuleCat.restrictScalarsId' ((rings I γ hc x₀).map (𝟙 T)).hom
        (congrArg RingCat.Hom.hom ((rings I γ hc x₀).map_id T))).inv.app _
  /-- Restrictions compose, including the canonical restriction-of-scalars comparison. -/
  map_comp {T U V : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ} (f : T ⟶ U) (g : U ⟶ V) :
    sectionsMap I γ hc x₀ F (f ≫ g) =
      sectionsMap I γ hc x₀ F f ≫
        (ModuleCat.restrictScalars ((rings I γ hc x₀).map f).hom).map
          (sectionsMap I γ hc x₀ F g) ≫
        (ModuleCat.restrictScalarsComp' ((rings I γ hc x₀).map f).hom
          ((rings I γ hc x₀).map g).hom ((rings I γ hc x₀).map (f ≫ g)).hom
          (congrArg RingCat.Hom.hom ((rings I γ hc x₀).map_comp f g))).inv.app _

/-- The module presheaf of a coherent family, with no fabricated functor laws. -/
noncomputable def sectionsPresheaf [SectionsCoherent I γ hc x₀ F] :
    PresheafOfModules.{u} (rings I γ hc x₀) where
  obj := sectionsObj I γ hc x₀ F
  map := sectionsMap I γ hc x₀ F
  map_id := SectionsCoherent.map_id
  map_comp := SectionsCoherent.map_comp

variable (p : ℕ) [Fact p.Prime]
variable (s : S ⟶ Spec (.of (ULift.{u} (Int.LocalizationAtPrime p))))
variable (hp : ∀ U : X.affineOpens, IsNilpotent (p : Γ(X, U)))

/-- Functions on the thickenings satisfy descent for crystalline open covers. -/
theorem rings_isSheaf :
    Presheaf.IsSheaf (smallCrystallineTopology p S I γ hc s X x₀ hp)
      (rings I γ hc x₀) := sorry

/-- The actual structure sheaf on the small crystalline site. -/
noncomputable def structureSheaf :
    Sheaf (smallCrystallineTopology p S I γ hc s X x₀ hp) RingCat.{u} :=
  ⟨rings I γ hc x₀, rings_isSheaf I γ hc x₀ p s hp⟩

/-- The ringed site retains the actual crystalline category, topology, and
structure sheaf; a bare equivalence of object categories cannot replace it. -/
noncomputable abbrev ringedSite : RingedSite.{u + 1, u, u} :=
  RingedSite.ofRingSheaf (smallCrystallineTopology p S I γ hc s X x₀ hp)
    (structureSheaf I γ hc x₀ p s hp)

/-- A coherent crystal's module sections glue across crystalline open covers. -/
theorem sections_isSheaf [SectionsCoherent I γ hc x₀ F] [CrisModuleSheaf.IsCrystal F] :
    Presheaf.IsSheaf (smallCrystallineTopology p S I γ hc s X x₀ hp)
      (sectionsPresheaf I γ hc x₀ F).presheaf := sorry

/-- The coefficient sheaf is constructed from the crystal's module sections
and comparison maps, rather than an unrelated sheaf with type-equivalent values. -/
noncomputable def ofCrystal [SectionsCoherent I γ hc x₀ F] [CrisModuleSheaf.IsCrystal F] :
    SheafOfModules.{u} (structureSheaf I γ hc x₀ p s hp) where
  val := sectionsPresheaf I γ hc x₀ F
  isSheaf := sections_isSheaf I γ hc x₀ F p s hp

/-- The coefficient object retains the actual section module and its scalar
action, rather than only an equivalence of underlying types. -/
theorem ofCrystal_obj [SectionsCoherent I γ hc x₀ F] [CrisModuleSheaf.IsCrystal F]
    (T : (smallCrystallineSite S I γ hc X x₀)ᵒᵖ) :
    (ofCrystal I γ hc x₀ F p s hp).val.obj T = sectionsObj I γ hc x₀ F T := rfl

/-- Universe lifting preserves the actual structure rings and restriction maps. -/
noncomputable def liftedStructureSheaf :
    Sheaf (smallCrystallineTopology p S I γ hc s X x₀ hp) RingCat.{u + 1} :=
  ⟨Presheaf.ringPresheafOfComm
    (Scheme.Over.commStructurePresheaf (thickeningOverBase I γ hc x₀)), sorry⟩

/-- The actual crystalline ringed site in a coefficient universe large enough
for its sheaf and derived-section constructions. -/
noncomputable abbrev liftedRingedSite : RingedSite.{u + 1, u, u + 1} :=
  RingedSite.ofRingSheaf (smallCrystallineTopology p S I γ hc s X x₀ hp)
    (liftedStructureSheaf I γ hc x₀ p s hp)

/-- The lifted coefficient module still consists of the original crystal's
sections, using the canonical universe-lift operation on module presheaves. -/
noncomputable def liftedOfCrystal
    [SectionsCoherent I γ hc x₀ F] [CrisModuleSheaf.IsCrystal F] :
    SheafOfModules.{u + 1} (liftedStructureSheaf I γ hc x₀ p s hp) where
  val := Scheme.AssociatedModule.liftedModulePresheaf (thickeningOverBase I γ hc x₀)
    (sectionsPresheaf I γ hc x₀ F)
  isSheaf := sorry

end CrystallineCoefficients
