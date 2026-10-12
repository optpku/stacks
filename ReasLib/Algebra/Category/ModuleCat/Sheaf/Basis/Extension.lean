/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Topology.Sheaves.AddCommGrpCat
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Sheaves.Sheaf
public import Mathlib.Topology.Sheaves.Presheaf
public import Mathlib.Topology.Sheaves.Stalks
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import ReasLib.Topology.Sheaves.Basis.Comparison
public import ReasLib.Topology.Sheaves.Basis.Algebraic.Restriction
public import ReasLib.Algebra.Category.Ring.Sheaf

/-!
# Extension of module sheaves from a topological basis

For a module sheaf on the site induced by a topological basis, this module constructs its extension
to all opens. The scalar action is reconstructed from locally representable families of basis-stalk
elements, retaining the canonical compatibility on basis opens.
-/

@[expose] public section

open CategoryTheory Opposite TopCat TopologicalSpace
open CategoryTheory.Limits
open BasisSiteSheaf

noncomputable section

universe u

section

variable {X : TopCat.{u}} {B : Set (Opens X)}
variable [basisFact : Fact (Opens.IsBasis B)]

namespace BasisSiteSheaf

/-- The underlying additive basis sheaf of a sheaf of `𝒪`-modules. -/
public abbrev moduleAddSheaf
    (𝒪 : BasisSiteSheaf RingCat B) (ℱ : SheafOfModules 𝒪) :
    BasisSiteSheaf AddCommGrpCat B :=
  ((SheafOfModules.toSheaf 𝒪).obj ℱ)

/-- A section of the extension sheaf on an arbitrary open determines a
family of basis stalk elements by taking its germs and transporting them back along the canonical
stalk comparison isomorphism. -/
public abbrev extendSectionToStalkFamily
    (G : BasisSiteSheaf AddCommGrpCat.{u} B) (U : Opens X) :
    (G.extend basisFact.out).presheaf.obj (op U) → ∀ x : U, G.stalk x.1 :=
  fun s x ↦
    inv (BasisSiteSheaf.stalkComparison G basisFact.out x.1) ((G.extend basisFact.out).presheaf.germ U x.1 x.2 s)

/-- A family of basis stalk elements on an arbitrary open is locally
representable if every point admits a basis neighborhood inside the open on which the family is
induced by an honest basis section. We record the witness after applying `stalkComparison`, since
that is the bridge used by the extension sheaf germs. -/
public def IsLocallyRepresentable
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    (U : Opens X) (t : ∀ x : U, G.stalk x.1) : Prop :=
  ∀ x : U,
    ∃ (V : BasisOpen B) (hVU : V.1 ≤ U) (_ : x.1 ∈ V.1) (sV : G.presheaf.obj (op V)),
      ∀ y : V.1,
        BasisSiteSheaf.stalkComparison G basisFact.out y.1 (t ⟨y.1, hVU y.2⟩) =
          (G.extend basisFact.out).presheaf.germ V.1 y.1 y.2
            (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op V) sV)

/-- After reapplying `stalkComparison`, the stalk family extracted from a
global section recovers the original germ of that section. -/
private theorem stalkComparison_extendSectionToStalkFamily
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    (U : Opens X) (s : (G.extend basisFact.out).presheaf.obj (op U)) (x : U) :
    BasisSiteSheaf.stalkComparison G basisFact.out x.1 (extendSectionToStalkFamily G U s x) =
      (G.extend basisFact.out).presheaf.germ U x.1 x.2 s := by
  -- This is the inverse-after-forward cancellation for the stalk comparison isomorphism.
  simp [extendSectionToStalkFamily]

/-- Two sections of the additive extension are equal once their induced
basis-stalk families agree pointwise. -/
private theorem extendSections_ext
    (G : BasisSiteSheaf AddCommGrpCat.{u} B) {U : Opens X}
    {s t : (G.extend basisFact.out).presheaf.obj (op U)}
    (hst : extendSectionToStalkFamily G U s = extendSectionToStalkFamily G U t) :
    s = t := by
  -- Compare germs pointwise after transporting back to ordinary stalks via `stalkComparison`.
  apply TopCat.Presheaf.section_ext (G.extend basisFact.out) U s t
  intro x hx
  have hpoint := congrFun hst ⟨x, hx⟩
  simpa [extendSectionToStalkFamily] using
    congrArg (BasisSiteSheaf.stalkComparison G basisFact.out x) hpoint

/-- The arbitrary-open basis-stalk-family map is injective. -/
public theorem extendSectionToStalkFamily_injective
    (G : BasisSiteSheaf AddCommGrpCat.{u} B) (U : Opens X) :
    Function.Injective (extendSectionToStalkFamily G U) := by
  intro s t hst
  exact extendSections_ext G hst

/-- Every actual section of `G.extend basisFact.out` yields a locally representable
basis-stalk family by restricting to a basis neighborhood and then pulling back along the
comparison isomorphism on that basis open. -/
private theorem extendSectionToStalkFamily_isLocallyRepresentable
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    (U : Opens X) (s : (G.extend basisFact.out).presheaf.obj (op U)) :
    IsLocallyRepresentable G U (extendSectionToStalkFamily G U s) := by
  intro x
  -- Choose a basis neighborhood inside `U`, then use the inverse basis comparison there.
  obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVU⟩ :=
    (basisFact.out).exists_subset_of_mem_open x.2 U.2
  let Vb : BasisOpen B := ⟨V, hVB⟩
  let iVU : V ⟶ U := homOfLE hVU
  let sV : G.presheaf.obj (op Vb) :=
    BasisSiteSheaf.restrictExtendComponentInv G basisFact.out (op Vb)
      ((G.extend basisFact.out).presheaf.map iVU.op s)
  refine ⟨Vb, hVU, hxV, sV, ?_⟩
  intro y
  -- On this basis neighborhood, the restricted extension section has the same germs as `s`.
  have hsV :
      BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op Vb) sV =
        (G.extend basisFact.out).presheaf.map iVU.op s := by
    dsimp [sV]
    simpa using
      CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id G basisFact.out (op Vb))
        ((G.extend basisFact.out).presheaf.map iVU.op s)
  calc
    BasisSiteSheaf.stalkComparison G basisFact.out y.1
        (extendSectionToStalkFamily G U s ⟨y.1, hVU y.2⟩) =
      (G.extend basisFact.out).presheaf.germ U y.1 (hVU y.2) s := by
        simpa using
          stalkComparison_extendSectionToStalkFamily G U s ⟨y.1, hVU y.2⟩
    _ = (G.extend basisFact.out).presheaf.germ V y.1 y.2 ((G.extend basisFact.out).presheaf.map iVU.op s) := by
        symm
        simpa [iVU] using (G.extend basisFact.out).presheaf.germ_res_apply iVU y.1 y.2 s
    _ = (G.extend basisFact.out).presheaf.germ V y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op Vb) sV) := by
        rw [hsV]

/-- A locally representable basis-stalk family on an arbitrary open
glues to a unique section of the extension sheaf. -/
public theorem existsUniqueSectionOfIsLocallyRepresentable
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    (U : Opens X) (t : ∀ x : U, G.stalk x.1)
    (ht : IsLocallyRepresentable G U t) :
    ∃! s : (G.extend basisFact.out).presheaf.obj (op U), extendSectionToStalkFamily G U s = t := by
  classical
  choose V hVU hxV sV hsV using ht
  let W : U → Opens X := fun x ↦ (V x).1
  let iWU : ∀ x : U, W x ⟶ U := fun x ↦ homOfLE (hVU x)
  let sf : ∀ x : U, (G.extend basisFact.out).presheaf.obj (op (W x)) := fun x ↦
    BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op (V x)) (sV x)
  have hcover : U ≤ iSup W := by
    intro x hxU
    exact (le_iSup W ⟨x, hxU⟩) (hxV ⟨x, hxU⟩)
  have hcompat : TopCat.Presheaf.IsCompatible (G.extend basisFact.out).presheaf W sf := by
    intro x y
    -- Equality on overlaps is checked on germs, where both local sections realize the same family.
    apply TopCat.Presheaf.section_ext (G.extend basisFact.out) (W x ⊓ W y)
    intro z hz
    have hzWx : z ∈ W x := (inf_le_left : W x ⊓ W y ≤ W x) hz
    have hzWy : z ∈ W y := (inf_le_right : W x ⊓ W y ≤ W y) hz
    have hxy :
        (⟨z, hVU x hzWx⟩ : U) = ⟨z, hVU y hzWy⟩ := Subtype.ext rfl
    calc
      (G.extend basisFact.out).presheaf.germ (W x ⊓ W y) z hz
          ((G.extend basisFact.out).presheaf.map (Opens.infLELeft (W x) (W y)).op (sf x)) =
        (G.extend basisFact.out).presheaf.germ (W x) z hzWx (sf x) := by
          simpa using
            (G.extend basisFact.out).presheaf.germ_res_apply (Opens.infLELeft (W x) (W y)) z hz (sf x)
      _ = BasisSiteSheaf.stalkComparison G basisFact.out z (t ⟨z, hVU x hzWx⟩) := by
          symm
          exact hsV x ⟨z, hzWx⟩
      _ = BasisSiteSheaf.stalkComparison G basisFact.out z (t ⟨z, hVU y hzWy⟩) := by
          cases hxy
          rfl
      _ = (G.extend basisFact.out).presheaf.germ (W y) z hzWy (sf y) := by
          exact hsV y ⟨z, hzWy⟩
      _ = (G.extend basisFact.out).presheaf.germ (W x ⊓ W y) z hz
          ((G.extend basisFact.out).presheaf.map (Opens.infLERight (W x) (W y)).op (sf y)) := by
          symm
          simpa using
            (G.extend basisFact.out).presheaf.germ_res_apply (Opens.infLERight (W x) (W y)) z hz (sf y)
  obtain ⟨s, hs, hs_unique⟩ := (G.extend basisFact.out).existsUnique_gluing' W U iWU hcover sf hcompat
  have hs_eq : extendSectionToStalkFamily G U s = t := by
    funext x
    -- The glued section has the prescribed germ on the chosen basis neighborhood around `x`.
    have hcompare :
        BasisSiteSheaf.stalkComparison G basisFact.out x.1 (t x) =
          (G.extend basisFact.out).presheaf.germ U x.1 x.2 s := by
      calc
        BasisSiteSheaf.stalkComparison G basisFact.out x.1 (t x) =
            (G.extend basisFact.out).presheaf.germ (W x) x.1 (hxV x) (sf x) := by
              simpa [W, sf, iWU] using hsV x ⟨x.1, hxV x⟩
        _ = (G.extend basisFact.out).presheaf.germ (W x) x.1 (hxV x)
              ((G.extend basisFact.out).presheaf.map (iWU x).op s) := by
              rw [← hs x]
        _ = (G.extend basisFact.out).presheaf.germ U x.1 x.2 s := by
              simpa [W, iWU] using
                (G.extend basisFact.out).presheaf.germ_res_apply (iWU x) x.1 (hxV x) s
    change inv (BasisSiteSheaf.stalkComparison G basisFact.out x.1)
        ((G.extend basisFact.out).presheaf.germ U x.1 x.2 s) = t x
    rw [← hcompare]
    simp
  refine ⟨s, hs_eq, ?_⟩
  · intro s' hs'
    exact extendSectionToStalkFamily_injective G U (by rw [hs', hs_eq])

/-- Reconstructing the basis-stalk family coming from a basis section
returns the canonical extension section on that basis open. -/
private theorem sectionOfIsLocallyRepresentable_eq_restrictExtend
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    (V : BasisOpen B) (sV : G.presheaf.obj (op V)) :
    let t := extendSectionToStalkFamily G V.1
      (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op V) sV)
    ∃! s : (G.extend basisFact.out).presheaf.obj (op V.1), extendSectionToStalkFamily G V.1 s = t := by
  let t := extendSectionToStalkFamily G V.1
    (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op V) sV)
  have ht :
      IsLocallyRepresentable G V.1 t :=
    extendSectionToStalkFamily_isLocallyRepresentable G V.1
      (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op V) sV)
  simpa [t] using
    existsUniqueSectionOfIsLocallyRepresentable G V.1 t ht

/-- A basis-open witness for local representability stays valid after
restricting the witnessing section to a smaller basis open. -/
private theorem restrictLocalRepresentabilityWitness
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    {U : Opens X} {t : ∀ x : U, G.stalk x.1}
    {V W : BasisOpen B}
    (hVU : V.1 ≤ U) (hWV : W.1 ≤ V.1)
    (sV : G.presheaf.obj (op V))
    (hsV : ∀ y : V.1,
      BasisSiteSheaf.stalkComparison G basisFact.out y.1 (t ⟨y.1, hVU y.2⟩) =
        (G.extend basisFact.out).presheaf.germ V.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op V) sV)) :
    ∀ y : W.1,
      BasisSiteSheaf.stalkComparison G basisFact.out y.1 (t ⟨y.1, hVU (hWV y.2)⟩) =
        (G.extend basisFact.out).presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op W)
            (G.presheaf.map
              ((ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWV)).op) sV)) := sorry
/-
  intro y
  let iWV : W ⟶ V :=
    ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWV)
  have hnat :=
    CategoryTheory.congr_fun
      (BasisSiteSheaf.restrictExtendHom_naturality G basisFact.out (i := iWV.op)) sV
  -- Naturality identifies the restricted extension section with the extension of the restricted
  -- basis section on the smaller basis open.
  calc
    BasisSiteSheaf.stalkComparison G basisFact.out y.1 (t ⟨y.1, hVU (hWV y.2)⟩) =
        (G.extend basisFact.out).presheaf.germ V.1 y.1 (hWV y.2)
          (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op V) sV) := by
          simpa using hsV ⟨y.1, hWV y.2⟩
    _ = (G.extend basisFact.out).presheaf.germ W.1 y.1 y.2
          ((G.extend basisFact.out).presheaf.map iWV.hom.op
            (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op V) sV)) := by
          symm
          simpa [iWV] using
            (G.extend basisFact.out).presheaf.germ_res_apply iWV.hom y.1 y.2
              (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op V) sV)
    _ = (G.extend basisFact.out).presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op W)
            (G.presheaf.map iWV.op sV)) := by
          simpa [iWV] using congrArg
            ((G.extend basisFact.out).presheaf.germ W.1 y.1 y.2) hnat.symm
-/

/-- The basis stalk of the underlying additive sheaf carries the
canonical module structure over the basis stalk of the ring sheaf, obtained by taking the filtered
colimit of the module structures on basis neighborhoods. -/
public noncomputable instance instModuleStalk
    (𝒪 : BasisSiteSheaf RingCat B) (ℱ : SheafOfModules 𝒪) (x : X) :
    Module (𝒪.stalk x) ((moduleAddSheaf 𝒪 ℱ).stalk x) := by
  -- Local instance justification (proof-local temporary data): filteredness is used only to construct the stalk-module colimit inside this instance proof.
  letI : IsFiltered ((BasisOpenNhds B x)ᵒᵖ) :=
    basisOpenNhds_isFiltered (B := B) basisFact.out x
  -- Local instance justification (proof-local temporary data): this canonical RingCat colimit witness is scoped to the stalk-module construction.
  letI : HasColimit (𝒪.stalkDiagram x) :=
    (RingCat.Colimits.hasColimits_ringCat.has_colimits_of_shape
      ((BasisOpenNhds B x)ᵒᵖ)).has_colimit (𝒪.stalkDiagram x)
  -- Local instance justification (proof-local temporary data): this canonical AddCommGrpCat colimit witness is scoped to the stalk-module construction.
  letI : HasColimit ((moduleAddSheaf 𝒪 ℱ).stalkDiagram x) :=
    AddCommGrpCat.hasColimit ((moduleAddSheaf 𝒪 ℱ).stalkDiagram x)
  -- Local instance justification (proof-local temporary data): the objectwise module instances are required only by `Limits.IsColimit.module` in this proof.
  letI (i : (BasisOpenNhds B x)ᵒᵖ) :
      Module ((𝒪.stalkDiagram x).obj i) (((moduleAddSheaf 𝒪 ℱ).stalkDiagram x).obj i) := by
    -- Each basis neighborhood carries the original module structure from `ℱ`.
    change Module (𝒪.1.obj (op (unop i).obj)) (ℱ.val.obj (op (unop i).obj))
    infer_instance
  -- The basis stalk is the filtered colimit of the module fibers on basis neighborhoods.
  exact Limits.IsColimit.module (𝒪.stalkDiagram x) ((moduleAddSheaf 𝒪 ℱ).stalkDiagram x)
    (fun {i j} f r m ↦ by
      -- On each basis neighborhood, semilinearity is exactly the original presheaf module axiom.
      change (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) (r • m) =
        (ConcreteCategory.hom (𝒪.1.map f.unop.hom.op)) r •
          (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) m
      exact ℱ.val.map_smul f.unop.hom.op r m)
    (Limits.colimit.isColimit _) (Limits.colimit.isColimit _)

/-- An arbitrary-open section of the extended ring sheaf determines a
family of basis stalk elements by transporting its germs back along the canonical stalk
comparison. -/
public abbrev extendRingSectionToStalkFamily
    (𝒪 : BasisSiteSheaf RingCat B) (U : Opens X) :
    (𝒪.extend basisFact.out).presheaf.obj (op U) → ∀ x : U, 𝒪.stalk x.1 :=
  fun r x ↦
    inv (BasisSiteSheaf.stalkComparison 𝒪 basisFact.out x.1) ((𝒪.extend basisFact.out).presheaf.germ U x.1 x.2 r)

/-- Reapplying the stalk comparison to the extracted ring stalk family
recovers the original germ. -/
private theorem stalkComparison_extendRingSectionToStalkFamily
    (𝒪 : BasisSiteSheaf RingCat B)
    (U : Opens X) (r : (𝒪.extend basisFact.out).presheaf.obj (op U)) (x : U) :
    BasisSiteSheaf.stalkComparison 𝒪 basisFact.out x.1 (extendRingSectionToStalkFamily 𝒪 U r x) =
      (𝒪.extend basisFact.out).presheaf.germ U x.1 x.2 r := by
  -- This is the inverse-after-forward cancellation for the ring stalk comparison isomorphism.
  simp [extendRingSectionToStalkFamily]

/-- The stalk comparison sends the basis-open representative of a
section to the corresponding germ of its extension on that basis neighborhood. -/
private theorem stalkComparison_basisOpen_eq_germ
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    (W : BasisOpen B) (y : W.1) (sW : G.presheaf.obj (op W)) :
    BasisSiteSheaf.stalkComparison G basisFact.out y.1
      (colimit.ι (G.stalkDiagram y.1) (op ⟨W, y.2⟩) sW) =
        (G.extend basisFact.out).presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op W) sW) := sorry
/-
  letI : Functor.Final (basisOpenNhdsToOpenNhds B y.1).op :=
    basisOpenNhdsToOpenNhds_final basisFact.out y.1
  let j : (BasisOpenNhds B y.1)ᵒᵖ := op ⟨W, y.2⟩
  have h₁ :
      colimit.ι (G.stalkDiagram y.1) j ≫
          (HasColimit.isoOfNatIso (G.stalkDiagramIso basisFact.out y.1)).hom ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ (G.extend basisFact.out).presheaf)).hom =
        (G.stalkDiagramIso basisFact.out y.1).hom.app j ≫
          colimit.ι (G.extendStalkDiagram basisFact.out y.1) j ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ (G.extend basisFact.out).presheaf)).hom := by
    -- First normalize the comparison coming from the diagram isomorphism.
    simpa [Category.assoc] using HasColimit.isoOfNatIso_ι_hom (G.stalkDiagramIso basisFact.out y.1) j
  have h₂base := Functor.Final.ι_colimitIso_hom (basisOpenNhdsToOpenNhds B y.1).op
    ((OpenNhds.inclusion y.1).op ⋙ (G.extend basisFact.out).presheaf) j
  have h₂ :
      (G.stalkDiagramIso basisFact.out y.1).hom.app j ≫
          colimit.ι (G.extendStalkDiagram basisFact.out y.1) j ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ (G.extend basisFact.out).presheaf)).hom =
        (G.stalkDiagramIso basisFact.out y.1).hom.app j ≫ (G.extend basisFact.out).presheaf.germ W.1 y.1 y.2 := by
    -- Then pass from the basis-neighborhood colimit to the ordinary germ on `W`.
    simpa [j, BasisSiteSheaf.extendStalkDiagram, Category.assoc] using
      congrArg (fun k ↦ (G.stalkDiagramIso basisFact.out y.1).hom.app j ≫ k) h₂base
  have h₃ :
      (G.stalkDiagramIso basisFact.out y.1).hom.app j ≫ (G.extend basisFact.out).presheaf.germ W.1 y.1 y.2 =
        G.restrictExtendComponentHom basisFact.out (op W) ≫ (G.extend basisFact.out).presheaf.germ W.1 y.1 y.2 := by
    -- On the chosen basis neighborhood, the diagram comparison is literally the restriction map.
    simp [j, BasisSiteSheaf.stalkDiagramIso, BasisSiteSheaf.restrictExtendComponentHom]
  exact CategoryTheory.congr_fun (h₁.trans (h₂.trans h₃)) sW
-/

/-- On a basis open, the extracted module stalk family is exactly the
stalk class of the original basis section. -/
private theorem extendSectionToStalkFamily_restrictExtend_eq_colimit_ι
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    (W : BasisOpen B) (sW : G.presheaf.obj (op W)) (y : W.1) :
    extendSectionToStalkFamily G W.1
        (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out (op W) sW) y =
      colimit.ι (G.stalkDiagram y.1) (op ⟨W, y.2⟩) sW := by
  -- Both sides become the same germ after applying the stalk comparison isomorphism.
  simpa [extendSectionToStalkFamily] using
    (congrArg (inv (BasisSiteSheaf.stalkComparison G basisFact.out y.1))
      (stalkComparison_basisOpen_eq_germ G W y sW)).symm

/-- On a basis open, the extracted ring stalk family is exactly the
stalk class of the original basis ring section. -/
private theorem extendRingSectionToStalkFamily_restrictExtend_eq_colimit_ι
    (𝒪 : BasisSiteSheaf RingCat B)
    (W : BasisOpen B) (rW : 𝒪.presheaf.obj (op W)) (y : W.1) :
    -- Local instance justification (defeq pin): the canonical RingCat colimit instance fixes the colimit injection occurring in this private law's type.
    letI : HasColimit (𝒪.stalkDiagram y.1) :=
      (RingCat.Colimits.hasColimits_ringCat.has_colimits_of_shape
        ((BasisOpenNhds B y.1)ᵒᵖ)).has_colimit (𝒪.stalkDiagram y.1)
    extendRingSectionToStalkFamily 𝒪 W.1
        (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op W) rW) y =
      colimit.ι (𝒪.stalkDiagram y.1) (op ⟨W, y.2⟩) rW := sorry
/-
  letI : Functor.Final (basisOpenNhdsToOpenNhds B y.1).op :=
    basisOpenNhdsToOpenNhds_final basisFact.out y.1
  let j : (BasisOpenNhds B y.1)ᵒᵖ := op ⟨W, y.2⟩
  have h₁ :
      colimit.ι (𝒪.stalkDiagram y.1) j ≫
          (HasColimit.isoOfNatIso (𝒪.stalkDiagramIso basisFact.out y.1)).hom ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ (𝒪.extend basisFact.out).presheaf)).hom =
        (𝒪.stalkDiagramIso basisFact.out y.1).hom.app j ≫
          colimit.ι (𝒪.extendStalkDiagram basisFact.out y.1) j ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ (𝒪.extend basisFact.out).presheaf)).hom := by
    -- Normalize the basis-stalk comparison exactly as in the additive case.
    simpa [Category.assoc] using HasColimit.isoOfNatIso_ι_hom (𝒪.stalkDiagramIso basisFact.out y.1) j
  have h₂base := Functor.Final.ι_colimitIso_hom (basisOpenNhdsToOpenNhds B y.1).op
    ((OpenNhds.inclusion y.1).op ⋙ (𝒪.extend basisFact.out).presheaf) j
  have h₂ :
      (𝒪.stalkDiagramIso basisFact.out y.1).hom.app j ≫
          colimit.ι (𝒪.extendStalkDiagram basisFact.out y.1) j ≫
          (Functor.Final.colimitIso (basisOpenNhdsToOpenNhds B y.1).op
            ((OpenNhds.inclusion y.1).op ⋙ (𝒪.extend basisFact.out).presheaf)).hom =
        (𝒪.stalkDiagramIso basisFact.out y.1).hom.app j ≫ (𝒪.extend basisFact.out).presheaf.germ W.1 y.1 y.2 := by
    -- Then pass from the basis-neighborhood colimit to the usual germ on `W`.
    simpa [j, BasisSiteSheaf.extendStalkDiagram, Category.assoc] using
      congrArg (fun k ↦ (𝒪.stalkDiagramIso basisFact.out y.1).hom.app j ≫ k) h₂base
  have h₃ :
      (𝒪.stalkDiagramIso basisFact.out y.1).hom.app j ≫ (𝒪.extend basisFact.out).presheaf.germ W.1 y.1 y.2 =
        𝒪.restrictExtendComponentHom basisFact.out (op W) ≫ (𝒪.extend basisFact.out).presheaf.germ W.1 y.1 y.2 := by
    -- On the chosen basis neighborhood, the diagram comparison is the restriction map.
    simp [j, BasisSiteSheaf.stalkDiagramIso, BasisSiteSheaf.restrictExtendComponentHom]
  have hcompare :
      BasisSiteSheaf.stalkComparison 𝒪 basisFact.out y.1
        (colimit.ι (𝒪.stalkDiagram y.1) j rW) =
          (𝒪.extend basisFact.out).presheaf.germ W.1 y.1 y.2
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op W) rW) := by
    exact CategoryTheory.congr_fun (h₁.trans (h₂.trans h₃)) rW
  -- Apply the inverse stalk comparison to the normalized germ equality.
  simpa [j, extendRingSectionToStalkFamily] using
    (congrArg (inv (BasisSiteSheaf.stalkComparison 𝒪 basisFact.out y.1)) hcompare).symm
-/

/-- Every actual section of `𝒪.extend basisFact.out` admits a basis-open local ring
witness describing its extracted ring stalk family. -/
private theorem existsBasisRingWitnessOfExtendSection
    (𝒪 : BasisSiteSheaf RingCat B)
    (U : Opens X) (r : (𝒪.extend basisFact.out).presheaf.obj (op U)) (x : U) :
    ∃ (V : BasisOpen B) (hVU : V.1 ≤ U) (_ : x.1 ∈ V.1) (rV : 𝒪.presheaf.obj (op V)),
      ∀ y : V.1,
        BasisSiteSheaf.stalkComparison 𝒪 basisFact.out y.1
          (extendRingSectionToStalkFamily 𝒪 U r ⟨y.1, hVU y.2⟩) =
            (𝒪.extend basisFact.out).presheaf.germ V.1 y.1 y.2
              (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op V) rV) := by
  obtain ⟨_, ⟨V, hVB, rfl⟩, hxV, hVU⟩ :=
    (basisFact.out).exists_subset_of_mem_open x.2 U.2
  let Vb : BasisOpen B := ⟨V, hVB⟩
  let iVU : V ⟶ U := homOfLE hVU
  let rV : 𝒪.presheaf.obj (op Vb) :=
    BasisSiteSheaf.restrictExtendComponentInv 𝒪 basisFact.out (op Vb)
      ((𝒪.extend basisFact.out).presheaf.map iVU.op r)
  refine ⟨Vb, hVU, hxV, rV, ?_⟩
  intro y
  have hrV :
      BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op Vb) rV =
        (𝒪.extend basisFact.out).presheaf.map iVU.op r := by
    dsimp [rV]
    simpa using
      CategoryTheory.congr_fun
        (BasisSiteSheaf.restrictExtend_component_inv_hom_id 𝒪 basisFact.out (op Vb))
        ((𝒪.extend basisFact.out).presheaf.map iVU.op r)
  -- On the chosen basis neighborhood, the restricted extension section has the same germs as `r`.
  calc
    BasisSiteSheaf.stalkComparison 𝒪 basisFact.out y.1
        (extendRingSectionToStalkFamily 𝒪 U r ⟨y.1, hVU y.2⟩) =
      (𝒪.extend basisFact.out).presheaf.germ U y.1 (hVU y.2) r := by
        simpa using
          stalkComparison_extendRingSectionToStalkFamily 𝒪 U r ⟨y.1, hVU y.2⟩
    _ = (𝒪.extend basisFact.out).presheaf.germ V y.1 y.2 ((𝒪.extend basisFact.out).presheaf.map iVU.op r) := by
        symm
        simpa [iVU] using (𝒪.extend basisFact.out).presheaf.germ_res_apply iVU y.1 y.2 r
    _ = (𝒪.extend basisFact.out).presheaf.germ V y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op Vb) rV) := by
        rw [hrV]

/-- On a common basis open, the pointwise product of the extracted ring
and module stalk families is represented by the basis section `rW • mW`. -/
private theorem basisOpenSMulWitness
    (𝒪 : BasisSiteSheaf RingCat B) (ℱ : SheafOfModules 𝒪)
    (W : BasisOpen B) (rW : 𝒪.presheaf.obj (op W))
    (mW : ℱ.val.obj (op W))
    (y : W.1) :
    BasisSiteSheaf.stalkComparison (moduleAddSheaf 𝒪 ℱ) basisFact.out y.1
        (extendRingSectionToStalkFamily 𝒪 W.1
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op W) rW) y •
          extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) W.1
            (BasisSiteSheaf.restrictExtendComponentHom
              (moduleAddSheaf 𝒪 ℱ) basisFact.out (op W) mW) y) =
      ((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.germ W.1 y.1 y.2
        (BasisSiteSheaf.restrictExtendComponentHom (moduleAddSheaf 𝒪 ℱ) basisFact.out
          (op W) (rW • mW)) := sorry
/-
  letI : IsFiltered ((BasisOpenNhds B y.1)ᵒᵖ) := basisOpenNhds_isFiltered (B := B) (hB := basisFact.out) y.1
  letI (i : (BasisOpenNhds B y.1)ᵒᵖ) :
      Module ((𝒪.stalkDiagram y.1).obj i)
        (((moduleAddSheaf 𝒪 ℱ).stalkDiagram y.1).obj i) := by
    change Module (𝒪.1.obj (op (unop i).obj))
      (ℱ.val.obj (op (unop i).obj))
    infer_instance
  let j : (BasisOpenNhds B y.1)ᵒᵖ := op ⟨W, y.2⟩
  -- Replace both extracted families by the corresponding colimit generators on `W`.
  calc
    BasisSiteSheaf.stalkComparison (moduleAddSheaf 𝒪 ℱ) basisFact.out y.1
        (extendRingSectionToStalkFamily 𝒪 W.1
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op W) rW) y •
          extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) W.1
            (BasisSiteSheaf.restrictExtendComponentHom
              (moduleAddSheaf 𝒪 ℱ) basisFact.out (op W) mW) y) =
      BasisSiteSheaf.stalkComparison (moduleAddSheaf 𝒪 ℱ) basisFact.out y.1
        (colimit.ι ((moduleAddSheaf 𝒪 ℱ).stalkDiagram y.1) j (rW • mW)) := by
          rw [extendRingSectionToStalkFamily_restrictExtend_eq_colimit_ι 𝒪 W rW y]
          rw [extendSectionToStalkFamily_restrictExtend_eq_colimit_ι
            (moduleAddSheaf 𝒪 ℱ) W mW y]
          -- The filtered-colimit module structure is generated by the literal basis-open formula.
          simpa [j] using congrArg
            (BasisSiteSheaf.stalkComparison (moduleAddSheaf 𝒪 ℱ) basisFact.out y.1)
            ((Limits.IsColimit.ι_smul (𝒪.stalkDiagram y.1)
              ((moduleAddSheaf 𝒪 ℱ).stalkDiagram y.1)
              (fun {i j} f r m ↦ by
                change (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) (r • m) =
                  (ConcreteCategory.hom (𝒪.1.map f.unop.hom.op)) r •
                    (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) m
                exact ℱ.val.map_smul f.unop.hom.op r m)
              (Limits.colimit.isColimit _) (Limits.colimit.isColimit _) j rW mW).symm)
    _ = ((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom (moduleAddSheaf 𝒪 ℱ) basisFact.out
            (op W) (rW • mW)) := by
          simpa [j] using
            stalkComparison_basisOpen_eq_germ (moduleAddSheaf 𝒪 ℱ) W y (rW • mW)
-/

/-- Restricting a ring witness to a smaller basis open preserves the
same local representation statement. -/
private theorem restrictLocalRingWitness
    (𝒪 : BasisSiteSheaf RingCat B)
    {U : Opens X} {t : ∀ x : U, 𝒪.stalk x.1}
    {V W : BasisOpen B}
    (hVU : V.1 ≤ U) (hWV : W.1 ≤ V.1)
    (rV : 𝒪.presheaf.obj (op V))
    (hrV : ∀ y : V.1,
      BasisSiteSheaf.stalkComparison 𝒪 basisFact.out y.1 (t ⟨y.1, hVU y.2⟩) =
        (𝒪.extend basisFact.out).presheaf.germ V.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op V) rV)) :
    ∀ y : W.1,
      BasisSiteSheaf.stalkComparison 𝒪 basisFact.out y.1 (t ⟨y.1, hVU (hWV y.2)⟩) =
        (𝒪.extend basisFact.out).presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op W)
            (𝒪.presheaf.map
              ((ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWV)).op) rV)) := sorry
/-
  intro y
  let iWV : W ⟶ V :=
    ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWV)
  have hnat :=
    CategoryTheory.congr_fun
      (BasisSiteSheaf.restrictExtendHom_naturality 𝒪 basisFact.out (i := iWV.op)) rV
  -- Naturality identifies the restricted extension section with the extension of the restricted
  -- ring section on the smaller basis open.
  calc
    BasisSiteSheaf.stalkComparison 𝒪 basisFact.out y.1 (t ⟨y.1, hVU (hWV y.2)⟩) =
        (𝒪.extend basisFact.out).presheaf.germ V.1 y.1 (hWV y.2)
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op V) rV) := by
          simpa using hrV ⟨y.1, hWV y.2⟩
    _ = (𝒪.extend basisFact.out).presheaf.germ W.1 y.1 y.2
          ((𝒪.extend basisFact.out).presheaf.map iWV.hom.op
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op V) rV)) := by
          symm
          simpa [iWV] using
            (𝒪.extend basisFact.out).presheaf.germ_res_apply iWV.hom y.1 y.2
              (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op V) rV)
    _ = (𝒪.extend basisFact.out).presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op W)
            (𝒪.presheaf.map iWV.op rV)) := by
          simpa [iWV] using congrArg
            ((𝒪.extend basisFact.out).presheaf.germ W.1 y.1 y.2) hnat.symm
-/

/-- The pointwise product of the ring and module stalk families coming
from actual extension sections is again locally representable on a common basis refinement. -/
public theorem isLocallyRepresentable_pointwiseSMul
    (𝒪 : BasisSiteSheaf RingCat B) (ℱ : SheafOfModules 𝒪)
    (U : Opens X)
    (r : (𝒪.extend basisFact.out).presheaf.obj (op U))
    (m : ((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj (op U)) :
    IsLocallyRepresentable (moduleAddSheaf 𝒪 ℱ) U
      (fun x ↦ extendRingSectionToStalkFamily 𝒪 U r x •
        extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) U m x) := by
  intro x
  obtain ⟨Vr, hVrU, hxVr, rVr, hrVr⟩ := existsBasisRingWitnessOfExtendSection 𝒪 U r x
  obtain ⟨Vm, hVmU, hxVm, mVm, hmVm⟩ :=
    extendSectionToStalkFamily_isLocallyRepresentable
      (moduleAddSheaf 𝒪 ℱ) U m x
  obtain ⟨_, ⟨W', hWB, rfl⟩, hxW, hWsub⟩ := (basisFact.out).exists_subset_of_mem_open
    (show x.1 ∈ (Vr.1 ⊓ Vm.1 : Opens X) from ⟨hxVr, hxVm⟩)
    (Vr.1 ⊓ Vm.1).2
  let W : BasisOpen B := ⟨W', hWB⟩
  have hWVr : W.1 ≤ Vr.1 := le_trans hWsub inf_le_left
  have hWVm : W.1 ≤ Vm.1 := le_trans hWsub inf_le_right
  have hWU : W.1 ≤ U := le_trans hWVr hVrU
  let iWVr : W ⟶ Vr :=
    ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWVr)
  let iWVm : W ⟶ Vm :=
    ObjectProperty.homMk (P := fun Z : Opens X ↦ Z ∈ B) (homOfLE hWVm)
  let rW : 𝒪.presheaf.obj (op W) := 𝒪.presheaf.map iWVr.op rVr
  let mW : ℱ.val.obj (op W) := ℱ.val.map iWVm.op mVm
  refine ⟨W, hWU, hxW, rW • mW, ?_⟩
  intro y
  have hrW := restrictLocalRingWitness 𝒪 hVrU hWVr rVr hrVr y
  have hmW := restrictLocalRepresentabilityWitness
    (moduleAddSheaf 𝒪 ℱ) hVmU hWVm mVm hmVm y
  have hrEq :
      extendRingSectionToStalkFamily 𝒪 U r ⟨y.1, hWU y.2⟩ =
        extendRingSectionToStalkFamily 𝒪 W.1
          (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op W) rW) y := by
    -- The restricted ring witness on `W` represents the same stalk family as the original one.
    simpa [rW, extendRingSectionToStalkFamily] using
      congrArg (inv (BasisSiteSheaf.stalkComparison 𝒪 basisFact.out y.1))
        ((hrW.trans
          (stalkComparison_extendRingSectionToStalkFamily 𝒪 W.1
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op W) rW) y).symm))
  have hmEq :
      extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) U m ⟨y.1, hWU y.2⟩ =
        extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) W.1
          (BasisSiteSheaf.restrictExtendComponentHom (moduleAddSheaf 𝒪 ℱ) basisFact.out (op W) mW) y := by
    -- The same argument identifies the module stalk family with the restricted basis witness.
    simpa [mW, extendSectionToStalkFamily] using
      congrArg (inv (BasisSiteSheaf.stalkComparison (moduleAddSheaf 𝒪 ℱ) basisFact.out y.1))
        ((hmW.trans
          (stalkComparison_extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) W.1
            (BasisSiteSheaf.restrictExtendComponentHom (moduleAddSheaf 𝒪 ℱ) basisFact.out (op W) mW) y).symm))
  -- On the common basis refinement, both factors come from honest basis sections, so the local
  -- product is represented by their ordinary product section.
  calc
    BasisSiteSheaf.stalkComparison (moduleAddSheaf 𝒪 ℱ) basisFact.out y.1
        (extendRingSectionToStalkFamily 𝒪 U r ⟨y.1, hWU y.2⟩ •
          extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) U m
            ⟨y.1, hWU y.2⟩) =
      BasisSiteSheaf.stalkComparison (moduleAddSheaf 𝒪 ℱ) basisFact.out y.1
        (extendRingSectionToStalkFamily 𝒪 W.1
            (BasisSiteSheaf.restrictExtendComponentHom 𝒪 basisFact.out (op W) rW) y •
          extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) W.1
            (BasisSiteSheaf.restrictExtendComponentHom
              (moduleAddSheaf 𝒪 ℱ) basisFact.out (op W) mW) y) := by
          rw [hrEq, hmEq]
    _ = ((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.germ W.1 y.1 y.2
          (BasisSiteSheaf.restrictExtendComponentHom (moduleAddSheaf 𝒪 ℱ) basisFact.out
            (op W) (rW • mW)) := by
          simpa [rW, mW] using basisOpenSMulWitness 𝒪 ℱ W rW mW y

/-- The section reconstructed from the pointwise product family has that
same product family as its extracted basis-stalk family. -/
private theorem extendSectionToStalkFamily_smulReconstructed
    (𝒪 : BasisSiteSheaf RingCat B) (ℱ : SheafOfModules 𝒪)
    (U : Opens X)
    (r : (𝒪.extend basisFact.out).presheaf.obj (op U))
    (m : ((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj (op U)) :
    let G : BasisSiteSheaf AddCommGrpCat B := moduleAddSheaf 𝒪 ℱ
    let t : ∀ x : U, G.stalk x.1 := fun x ↦
      extendRingSectionToStalkFamily 𝒪 U r x • extendSectionToStalkFamily G U m x
    let s : (G.extend basisFact.out).presheaf.obj (op U) :=
      Classical.choose <|
        existsUniqueSectionOfIsLocallyRepresentable G U t
      (isLocallyRepresentable_pointwiseSMul 𝒪 ℱ U r m)
    extendSectionToStalkFamily G U s = t := by
  -- The chosen section is exactly the witness returned by the unique reconstruction theorem.
  simpa using
    (Classical.choose_spec
      (existsUniqueSectionOfIsLocallyRepresentable
        (moduleAddSheaf 𝒪 ℱ) U
        (fun x ↦ extendRingSectionToStalkFamily 𝒪 U r x •
          extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) U m x)
        (isLocallyRepresentable_pointwiseSMul 𝒪 ℱ U r m))).1

/-- The reconstructed pointwise stalk-family product defines the scalar
action on sections of the additive extension over an arbitrary open. -/
public noncomputable def extendModuleSectionSMul
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X) :
    (𝒪.extend basisFact.out).presheaf.obj (op U) →
      ((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj (op U) →
      ((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj (op U) :=
  fun r m ↦
    Classical.choose <|
      existsUniqueSectionOfIsLocallyRepresentable
        (moduleAddSheaf 𝒪 ℱ) U
        (fun x ↦ extendRingSectionToStalkFamily 𝒪 U r x •
          extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) U m x)
        (isLocallyRepresentable_pointwiseSMul 𝒪 ℱ U r m)

/-- Extracting basis stalks from the reconstructed scalar product
recovers the pointwise stalk-family product used to define it. -/
public theorem extendModuleSectionSMul_stalkFamily
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X)
    (r : (𝒪.extend basisFact.out).presheaf.obj (op U))
    (m : ((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj (op U)) :
    extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) U
        (extendModuleSectionSMul 𝒪 ℱ U r m) =
      fun x ↦
        extendRingSectionToStalkFamily 𝒪 U r x •
          extendSectionToStalkFamily (moduleAddSheaf 𝒪 ℱ) U m x := by
  -- The reconstructed section was chosen precisely so that its extracted family is this product.
  simpa [extendModuleSectionSMul] using
    extendSectionToStalkFamily_smulReconstructed 𝒪 ℱ U r m

/-- Restricting an extracted basis-stalk family to a smaller open is
computed by the ordinary restriction on germs. -/
private theorem extendSectionToStalkFamily_map
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    {U V : Opens X} (i : V ⟶ U)
    (s : (G.extend basisFact.out).presheaf.obj (op U)) (x : V) :
    extendSectionToStalkFamily G V ((G.extend basisFact.out).presheaf.map i.op s) x =
      extendSectionToStalkFamily G U s ⟨x.1, i.le x.2⟩ := by
  -- Both families become the same germ after applying the stalk comparison isomorphism.
  simpa [extendSectionToStalkFamily] using
    congrArg (inv (BasisSiteSheaf.stalkComparison G basisFact.out x.1))
      ((G.extend basisFact.out).presheaf.germ_res_apply i x.1 x.2 s)

/-- The ring-valued extracted stalk family restricts along germs in the
same way. -/
private theorem extendRingSectionToStalkFamily_map
    (𝒪 : BasisSiteSheaf RingCat B)
    {U V : Opens X} (i : V ⟶ U)
    (r : (𝒪.extend basisFact.out).presheaf.obj (op U)) (x : V) :
    extendRingSectionToStalkFamily 𝒪 V ((𝒪.extend basisFact.out).presheaf.map i.op r) x =
      extendRingSectionToStalkFamily 𝒪 U r ⟨x.1, i.le x.2⟩ := by
  -- This is the ring-valued analogue of `extendSectionToStalkFamily_map`.
  simpa [extendRingSectionToStalkFamily] using
    congrArg (inv (BasisSiteSheaf.stalkComparison 𝒪 basisFact.out x.1))
      ((𝒪.extend basisFact.out).presheaf.germ_res_apply i x.1 x.2 r)

/-- Pointwise stalk families carry the natural scalar action induced by
the extracted ring stalk family of a section of `𝒪.extend basisFact.out`. -/
public noncomputable instance instModuleExtendStalkFamily
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X) :
    Module ((𝒪.extend basisFact.out).presheaf.obj (op U))
      (∀ x : U, (moduleAddSheaf 𝒪 ℱ).stalk x.1) where
  smul r t x := extendRingSectionToStalkFamily 𝒪 U r x • t x
  one_smul := by
    intro t
    -- The unit section acts stalkwise by the unit of each stalk module.
    funext x
    change extendRingSectionToStalkFamily 𝒪 U (1 : (𝒪.extend basisFact.out).presheaf.obj (op U)) x • t x =
      t x
    simp [extendRingSectionToStalkFamily]
  mul_smul := by
    intro r s t
    -- Multiplication of sections is computed pointwise on the extracted ring stalk family.
    funext x
    change extendRingSectionToStalkFamily 𝒪 U (r * s) x • t x =
      extendRingSectionToStalkFamily 𝒪 U r x •
        (extendRingSectionToStalkFamily 𝒪 U s x • t x)
    simp [extendRingSectionToStalkFamily, mul_smul]
  smul_zero := by
    intro r
    -- The pointwise action preserves the zero stalk family.
    funext x
    change extendRingSectionToStalkFamily 𝒪 U r x •
        (0 : (moduleAddSheaf 𝒪 ℱ).stalk x.1) =
      0
    simp
  smul_add := by
    intro r t₁ t₂
    -- Distributivity is reduced to the module law in each basis stalk.
    funext x
    change extendRingSectionToStalkFamily 𝒪 U r x • (t₁ x + t₂ x) =
      extendRingSectionToStalkFamily 𝒪 U r x • t₁ x +
        extendRingSectionToStalkFamily 𝒪 U r x • t₂ x
    simp [smul_add]
  zero_smul := by
    intro t
    -- The zero section acts trivially on every extracted basis stalk.
    funext x
    change extendRingSectionToStalkFamily 𝒪 U (0 : (𝒪.extend basisFact.out).presheaf.obj (op U)) x • t x =
      0
    simp [extendRingSectionToStalkFamily]
  add_smul := by
    intro r s t
    -- Addition of sections is computed pointwise on the extracted ring stalk family.
    funext x
    change extendRingSectionToStalkFamily 𝒪 U (r + s) x • t x =
      extendRingSectionToStalkFamily 𝒪 U r x • t x +
        extendRingSectionToStalkFamily 𝒪 U s x • t x
    simp [extendRingSectionToStalkFamily, add_smul]

/-- Extracting basis stalk families is an additive map on arbitrary-open
sections of the additive extension. -/
public def extendSectionToStalkFamilyAddMonoidHom
    (G : BasisSiteSheaf AddCommGrpCat.{u} B)
    (U : Opens X) :
    (G.extend basisFact.out).presheaf.obj (op U) →+ ∀ x : U, G.stalk x.1 where
  toFun := extendSectionToStalkFamily G U
  map_zero' := by
    -- Zero sections have zero germs, so the extracted family is pointwise zero.
    funext x
    simp [extendSectionToStalkFamily]
  map_add' s t := by
    -- Additivity is checked pointwise on germs and then transported back to basis stalks.
    funext x
    simp [extendSectionToStalkFamily]

/-- The reconstructed pointwise product equips the extension section
space on an open with a scalar action. -/
public noncomputable instance instSMulExtendModuleSection
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X) :
    SMul ((𝒪.extend basisFact.out).presheaf.obj (op U))
      (((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj (op U)) where
  smul := extendModuleSectionSMul 𝒪 ℱ U

/-- The reconstructed scalar action makes sections of the additive
extension over each open into a module over sections of `𝒪.extend basisFact.out`. -/
public noncomputable abbrev extendModuleSectionModule
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪)
    (U : Opens X) :
    Module ((𝒪.extend basisFact.out).presheaf.obj (op U))
      (((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj (op U)) :=
  Function.Injective.module ((𝒪.extend basisFact.out).presheaf.obj (op U))
    (extendSectionToStalkFamilyAddMonoidHom (moduleAddSheaf 𝒪 ℱ) U)
    (extendSectionToStalkFamily_injective (moduleAddSheaf 𝒪 ℱ) U)
    (extendModuleSectionSMul_stalkFamily 𝒪 ℱ U)

/-- The objectwise module structure is available uniformly for the
opposite-indexed presheaf objects used by `PresheafOfModules.ofPresheaf`. -/
public noncomputable instance instModuleExtendModuleSection
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪)
    (U : (Opens X)ᵒᵖ) :
    Module ((𝒪.extend basisFact.out).presheaf.obj U)
      (((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj U) := by
  -- This is just the objectwise module structure on the underlying open `U.unop`.
  simpa using
    (extendModuleSectionModule (𝒪 := 𝒪) (ℱ := ℱ) (U := U.unop))

/-- Restriction maps of the additive extension are semilinear for the
reconstructed section-level scalar action. -/
private theorem extendModulePresheafMap_smul
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪)
    {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (r : (𝒪.extend basisFact.out).presheaf.obj U)
    (m : ((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj U) :
    (((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.map i) (r • m) =
      (((𝒪.extend basisFact.out).presheaf.map i) r) •
        ((((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.map i) m) := sorry
/-
  let G : BasisSiteSheaf AddCommGrpCat B := moduleAddSheaf 𝒪 ℱ
  -- Compare the extracted basis-stalk families after restricting from `V.unop` to `U.unop`.
  apply extendSections_ext (G := G)
  funext x
  -- Restrict the left-hand section, expand both scalar products, and compare the resulting
  -- pointwise stalk families.
  calc
    extendSectionToStalkFamily G V.unop ((G.extend basisFact.out).presheaf.map i (r • m)) x =
      extendSectionToStalkFamily G U.unop (r • m) ⟨x.1, i.unop.le x.2⟩ := by
        simpa [G] using extendSectionToStalkFamily_map (G := G) i.unop (r • m) x
    _ = extendRingSectionToStalkFamily 𝒪 U.unop r ⟨x.1, i.unop.le x.2⟩ •
          extendSectionToStalkFamily G U.unop m ⟨x.1, i.unop.le x.2⟩ := by
        simpa [G] using congrFun (extendModuleSectionSMul_stalkFamily 𝒪 ℱ U.unop r m) ⟨x.1, i.unop.le x.2⟩
    _ = extendRingSectionToStalkFamily 𝒪 V.unop ((𝒪.extend basisFact.out).presheaf.map i r) x •
          extendSectionToStalkFamily G V.unop ((G.extend basisFact.out).presheaf.map i m) x := by
        rw [← extendRingSectionToStalkFamily_map (𝒪 := 𝒪) i.unop r x]
        rw [← extendSectionToStalkFamily_map (G := G) i.unop m x]
        have hi : i.unop.op = i := Quiver.Hom.unop_op i
        simpa [hi]
    _ = extendSectionToStalkFamily G V.unop
          ((((𝒪.extend basisFact.out).presheaf.map i) r) • (((G.extend basisFact.out).presheaf.map i) m)) x := by
        simpa [G] using
          (congrFun
            (extendModuleSectionSMul_stalkFamily 𝒪 ℱ V.unop
              (((𝒪.extend basisFact.out).presheaf.map i) r) (((G.extend basisFact.out).presheaf.map i) m)) x).symm
-/

/-- The presheaf of modules underlying the extension of a module sheaf from a topological basis. -/
public noncomputable def extendModuleVal
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪) :
    PresheafOfModules (𝒪.extend basisFact.out).obj :=
  PresheafOfModules.ofPresheaf
    (((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf)
    (by
      intro U V i r m
      exact extendModulePresheafMap_smul (𝒪 := 𝒪) (ℱ := ℱ) i r m)

/-- The underlying additive presheaf of the extended module presheaf satisfies the sheaf
condition. -/
public theorem extendModuleVal_isSheaf
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (extendModuleVal 𝒪 ℱ).presheaf := by
  -- The reconstructed module presheaf has exactly the additive extension as underlying presheaf.
  simpa [extendModuleVal] using
    (BasisSiteSheaf.extend (moduleAddSheaf 𝒪 ℱ) basisFact.out).2

/-- The generic extension construction for modules over a possibly noncommutative ring sheaf on
the basis site. -/
noncomputable def extendModule
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪) :
    SheafOfModules (𝒪.extend basisFact.out) where
  val := extendModuleVal 𝒪 ℱ
  isSheaf := extendModuleVal_isSheaf 𝒪 ℱ

/-- Extend a module sheaf over a commutative-ring sheaf from a topological basis, after passing to
the canonical underlying possibly noncommutative ring sheaf. -/
noncomputable def extendModuleOfComm
    (𝒪 : BasisSiteSheaf CommRingCat.{u} B)
    (ℱ : SheafOfModules (CategoryTheory.Sheaf.ringSheafOfComm
      (J := basisGrothendieckTopology B) 𝒪)) :
    SheafOfModules (BasisSiteSheaf.extend (CategoryTheory.Sheaf.ringSheafOfComm
      (J := basisGrothendieckTopology B) 𝒪) basisFact.out) where
  val := extendModuleVal
    (CategoryTheory.Sheaf.ringSheafOfComm (J := basisGrothendieckTopology B) 𝒪) ℱ
  isSheaf := extendModuleVal_isSheaf
    (CategoryTheory.Sheaf.ringSheafOfComm (J := basisGrothendieckTopology B) 𝒪) ℱ

/-- The underlying additive sheaf of `extendModule 𝒪 ℱ` is the canonical extension of the
underlying additive sheaf of `ℱ` from the basis site to `X`; their underlying presheaves agree
definitionally. -/
@[simp]
theorem extendModule_toSheaf
    (𝒪 : BasisSiteSheaf RingCat B)
    (ℱ : SheafOfModules 𝒪) :
    (SheafOfModules.toSheaf (𝒪.extend basisFact.out)).obj
        (extendModule 𝒪 ℱ) =
      BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ) basisFact.out := by
  -- Both sheaves have the same underlying additive presheaf, so they are equal by proof
  -- irrelevance in the sheaf predicate.
  apply ObjectProperty.FullSubcategory.ext
  rfl

/-- The restriction of the extended additive sheaf to a basis open carries the sectionwise module
structure constructed by `extendModule`. This named instance is the defeq bridge from the
underlying additive extension to the module-valued owner. -/
public instance instModuleRestrictExtendComponent
    (𝒪 : BasisSiteSheaf RingCat B) (ℱ : SheafOfModules 𝒪) (U : (BasisOpen B)ᵒᵖ) :
    Module (((basisOpenInclusion B).op ⋙ (𝒪.extend basisFact.out).presheaf).obj U)
      (((basisOpenInclusion B).op ⋙
          (BasisSiteSheaf.extend ((SheafOfModules.toSheaf 𝒪).obj ℱ) basisFact.out).presheaf).obj U) := by
  change Module ((𝒪.extend basisFact.out).presheaf.obj ((basisOpenInclusion B).op.obj U))
    (((moduleAddSheaf 𝒪 ℱ).extend basisFact.out).presheaf.obj ((basisOpenInclusion B).op.obj U))
  infer_instance

/-- On a basis open, the canonical comparison map from `ℱ` to the restriction of
`extendModule 𝒪 ℱ` is semilinear for the comparison map from `𝒪` to
`𝒪.extend basisFact.out`. -/
theorem extendModule_restrictExtendComponentHom_smul
    (𝒪 : BasisSiteSheaf RingCat B) (ℱ : SheafOfModules 𝒪) (U : (BasisOpen B)ᵒᵖ)
    (r : 𝒪.presheaf.obj U) (m : ℱ.val.obj U) :
    BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj ℱ) basisFact.out U (r • m) =
      𝒪.restrictExtendComponentHom basisFact.out U r •
        BasisSiteSheaf.restrictExtendComponentHom ((SheafOfModules.toSheaf 𝒪).obj ℱ) basisFact.out U m := sorry
/-
  let G : BasisSiteSheaf AddCommGrpCat B := moduleAddSheaf 𝒪 ℱ
  apply extendSections_ext (G := G)
  funext y
  letI : IsFiltered ((BasisOpenNhds B y.1)ᵒᵖ) := basisOpenNhds_isFiltered (B := B) (hB := basisFact.out) y.1
  letI (i : (BasisOpenNhds B y.1)ᵒᵖ) :
      Module ((𝒪.stalkDiagram y.1).obj i)
        ((G.stalkDiagram y.1).obj i) := by
    change Module (𝒪.1.obj (op (unop i).obj))
      (ℱ.val.obj (op (unop i).obj))
    infer_instance
  let j : (BasisOpenNhds B y.1)ᵒᵖ := op ⟨U.unop, y.2⟩
  -- On the basis open itself, the reconstructed scalar action is the original module action.
  calc
    extendSectionToStalkFamily G ((basisOpenInclusion B).obj U.unop)
        (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out U (r • m)) y =
      colimit.ι (G.stalkDiagram y.1) j (r • m) := by
        simpa [G, j] using
          extendSectionToStalkFamily_restrictExtend_eq_colimit_ι (G := G) U.unop (r • m) y
    _ = colimit.ι (𝒪.stalkDiagram y.1) j r • colimit.ι (G.stalkDiagram y.1) j m := by
      simpa [G, j] using
        Limits.IsColimit.ι_smul (𝒪.stalkDiagram y.1)
          (G.stalkDiagram y.1)
          (fun {i j} f r' m' ↦ by
            change (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) (r' • m') =
              (ConcreteCategory.hom (𝒪.1.map f.unop.hom.op)) r' •
                (ConcreteCategory.hom (ℱ.val.map f.unop.hom.op)) m'
            exact ℱ.val.map_smul f.unop.hom.op r' m')
          (Limits.colimit.isColimit _) (Limits.colimit.isColimit _) j r m
    _ = extendRingSectionToStalkFamily 𝒪 ((basisOpenInclusion B).obj U.unop)
          (𝒪.restrictExtendComponentHom basisFact.out U r) y •
        extendSectionToStalkFamily G ((basisOpenInclusion B).obj U.unop)
          (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out U m) y := by
        have hr :
            colimit.ι (𝒪.stalkDiagram y.1) j r =
              extendRingSectionToStalkFamily 𝒪 ((basisOpenInclusion B).obj U.unop)
                (𝒪.restrictExtendComponentHom basisFact.out U r) y := by
          simpa [j] using
            (extendRingSectionToStalkFamily_restrictExtend_eq_colimit_ι
              (𝒪 := 𝒪) U.unop r y).symm
        have hm :
            colimit.ι (G.stalkDiagram y.1) j m =
              extendSectionToStalkFamily G ((basisOpenInclusion B).obj U.unop)
                (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out U m) y := by
          simpa [G, j] using
            (extendSectionToStalkFamily_restrictExtend_eq_colimit_ι
              (G := G) U.unop m y).symm
        rw [hr, hm]
    _ = extendSectionToStalkFamily G ((basisOpenInclusion B).obj U.unop)
          (𝒪.restrictExtendComponentHom basisFact.out U r •
            BasisSiteSheaf.restrictExtendComponentHom G basisFact.out U m) y := by
        simpa [G] using
          (congrFun
            (extendModuleSectionSMul_stalkFamily 𝒪 ℱ ((basisOpenInclusion B).obj U.unop)
              (𝒪.restrictExtendComponentHom basisFact.out U r)
              (BasisSiteSheaf.restrictExtendComponentHom G basisFact.out U m)) y).symm
-/

end BasisSiteSheaf

end

namespace BasisSiteSheaf

variable {X : TopCat.{u}} {B : Set (Opens X)}

/-- Extend a module sheaf from a basis using an explicit basis proof. This is the public
proof-argument entry point; `extendModule` remains the lower-level instance-driven API for
constructions that already carry `Fact (Opens.IsBasis B)`. -/
noncomputable def extendModule_of_isBasis
    (hB : Opens.IsBasis B) (𝒪 : BasisSiteSheaf RingCat.{u} B)
    (ℱ : SheafOfModules 𝒪) :
    SheafOfModules (BasisSiteSheaf.extend 𝒪 hB) :=
  -- Local instance justification (defeq pin): the proof-explicit wrapper pins its explicit `hB` as the `Fact` required by the established lower-level construction.
  letI : Fact (Opens.IsBasis B) := ⟨hB⟩
  extendModule 𝒪 ℱ

/-- Extend a module sheaf over a commutative ring sheaf from a basis using an explicit basis
proof. This avoids requiring downstream callers to manufacture a `Fact` instance solely to use
the canonical extension. -/
noncomputable def extendModuleOfComm_of_isBasis
    (hB : Opens.IsBasis B) (𝒪 : BasisSiteSheaf CommRingCat.{u} B)
    (ℱ : SheafOfModules (CategoryTheory.Sheaf.ringSheafOfComm
      (J := basisGrothendieckTopology B) 𝒪)) :
    SheafOfModules (BasisSiteSheaf.extend
      (CategoryTheory.Sheaf.ringSheafOfComm (J := basisGrothendieckTopology B) 𝒪) hB) :=
  -- Local instance justification (defeq pin): the commutative proof-explicit wrapper pins its explicit `hB` as the `Fact` required by the established lower-level construction.
  letI : Fact (Opens.IsBasis B) := ⟨hB⟩
  extendModuleOfComm 𝒪 ℱ

end BasisSiteSheaf
