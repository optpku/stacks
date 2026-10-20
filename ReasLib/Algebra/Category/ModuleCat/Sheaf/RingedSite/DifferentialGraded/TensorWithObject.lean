module

public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Algebra.Category.Ring.Limits
public import ReasLib.Algebra.Category.DifferentialGraded.Endomorphism
public import ReasLib.Algebra.Category.DifferentialGraded.Functor.Homotopy
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction.Complex
public import ReasLib.Algebra.Homology.CochainComplex.DifferentialGraded
public import ReasLib.Algebra.Homology.DifferentialGradedModule.TensorProduct.Unit

/-!
# Tensoring with a complex on a ringed site

For a complex `K` of modules on a ringed site, this file constructs the sectionwise left action
of the ordinary endomorphism DGA `End(K)` on `K(U)`.  Relative tensor products with these
section modules are assembled into module presheaves and then sheafified.  The resulting
construction is the source-faithful DG functor `- ⊗_End(K) K` of Lemma 22.35.1 (09LV).

All enrichments and tensor products use the canonical coefficient ring `ℤ`.  The section and
DG-module carriers live in `max u v`, independently of the site-object and site-morphism universes.
-/

@[expose] public section

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits
open CochainComplex.HomComplex
open DifferentialGradedCategory
open scoped DifferentialGradedCategory
open SheafOfModules.RingedSite.ModuleSheafification

namespace SheafOfModules.RingedSite.TensorWithObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- Complexes of modules on the fixed ringed site. -/
@[stacks 09LV "complexes of modules on a ringed site"]
abbrev Complex :=
  CochainComplex (ringedSiteModuleCategory.{u, v, max u v, max u v} J O) ℤ

/-- The ordinary integral endomorphism DGA of a complex on the ringed site. -/
@[stacks 09LV "endomorphism DGA of a ringed-site complex"]
abbrev endDGA (K : Complex (J := J) (O := O)) :=
  DifferentialGradedCategory.endomorphismDGA (R := ℤ) K

/-- Right DG modules over the endomorphism DGA in the universe used by sectionwise tensoring. -/
@[stacks 09LV "right modules over the endomorphism DGA"]
abbrev Modules (K : Complex (J := J) (O := O)) :=
  DifferentialGradedModule.{0, max u v} (endDGA.{u, v} K)

/-- Degree `n` sections of `K` over `U`, viewed as an integral module. -/
@[stacks 09LV "degreewise sections of a ringed-site complex"]
abbrev Section (K : Complex (J := J) (O := O)) (U : Cᵒᵖ) (n : ℤ) :
    ModuleCat.{max u v} ℤ :=
  ModuleCat.of ℤ ((K.X n).val.obj U)

/-- Evaluation of a degree-`i` endomorphism on degree-`p` sections over `U`. -/
@[stacks 09LV "evaluation of a homogeneous endomorphism on sections"]
def actionValue (K : Complex (J := J) (O := O)) (U : Cᵒᵖ) (i p : ℤ)
    (a : (endDGA K).X i) (x : Section K U p) : Section K U (i + p) :=
  ((((a : Cochain K K i).v p (p + i) rfl) ≫
      eqToHom (congrArg K.X (add_comm p i))).val.app U) x

/-- The homogeneous endomorphism action on sections, as an integral bilinear map. -/
@[stacks 09LV "sectionwise endomorphism action"]
def action (K : Complex (J := J) (O := O)) (U : Cᵒᵖ) (i p : ℤ) :
    (endDGA K).X i →ₗ[ℤ] Section K U p →ₗ[ℤ] Section K U (i + p) where
  toFun a :=
    { toFun := actionValue K U i p a
      map_add' := sorry
      map_smul' := sorry }
  map_add' := sorry
  map_smul' := sorry

/-- Sections of `K` over `U`, with their explicit left action by the global endomorphism DGA. -/
@[stacks 09LV "sections as a left endomorphism module"]
def sectionModule (K : Complex (J := J) (O := O)) (U : Cᵒᵖ) :
    LeftDifferentialGradedModule (endDGA K) where
  X := Section K U
  d n :=
    { toFun := fun x ↦ (K.d n (n + 1)).val.app U x
      map_add' := sorry
      map_smul' := sorry }
  smul := action K U
  d_sq := sorry
  smul_one := sorry
  smul_mul := sorry
  comm_d := sorry

/-- Restriction of sections is a morphism of left `endDGA K`-modules. -/
@[stacks 09LV "restriction of endomorphism modules of sections"]
def restriction (K : Complex (J := J) (O := O)) {U V : Cᵒᵖ} (f : U ⟶ V) :
    sectionModule K U ⟶ sectionModule K V where
  hom n :=
    { toFun := fun x ↦ (K.X n).val.map f x
      map_add' := sorry
      map_smul' := sorry }
  comm_d := sorry
  comm_smul := sorry

/-- Multiplication by a local structure-ring section on a fixed homogeneous section module. -/
@[stacks 09LV "local scalar action on homogeneous sections"]
def scalarValue (K : Complex (J := J) (O := O)) (U : Cᵒᵖ) (n : ℤ)
    (r : (ringSheaf J O).obj.obj U) (x : Section K U n) : Section K U n :=
  r • x

/-- Multiplication by a local section of the structure sheaf is an endomorphism of the
left `endDGA K`-module of sections. -/
@[stacks 09LV "local scalar endomorphism of the section module"]
def scalarAction (K : Complex (J := J) (O := O)) (U : Cᵒᵖ)
    (r : (ringSheaf J O).obj.obj U) : sectionModule K U ⟶ sectionModule K U where
  hom n :=
    { toFun := scalarValue K U n r
      map_add' := sorry
      map_smul' := sorry }
  comm_d := sorry
  comm_smul := sorry

/-- The degree-`n` sectionwise relative tensor product before sheafification. -/
@[stacks 09LV "sectionwise relative tensor family"]
abbrev Family (K : Complex (J := J) (O := O))
    (M : Modules K) (U : Cᵒᵖ) (n : ℤ) :
    ModuleCat.{max u v} ℤ :=
  DifferentialGradedModule.TensorProduct.family M (sectionModule K U) n

/-- The structure-ring action on one degree of the sectionwise relative tensor product. -/
@[stacks 09LV "structure-ring action on the relative tensor family"]
def familyAction (K : Complex (J := J) (O := O))
    (M : Modules K) (U : Cᵒᵖ) (n : ℤ) :
    (ringSheaf J O).obj.obj U →+*
      Module.End ℤ (Family K M U n) where
  toFun r :=
    { toFun := DifferentialGradedModule.TensorProduct.mapLeftLinear M (scalarAction K U r) n
      map_add' := sorry
      map_smul' := sorry }
  map_one' := sorry
  map_mul' := sorry
  map_zero' := sorry
  map_add' := sorry

/-- The canonical `O(U)`-module structure on the sectionwise relative tensor product. -/
@[stacks 09LV "module structure on the relative tensor family"]
noncomputable instance familyModule (K : Complex (J := J) (O := O))
    (M : Modules K) (U : Cᵒᵖ) (n : ℤ) :
    Module ((ringSheaf J O).obj.obj U) (Family K M U n) :=
  Module.compHom _ (familyAction K M U n)

/-- Degree `n` of the relative tensor construction as a presheaf of `O`-modules. -/
@[stacks 09LV "degreewise relative tensor presheaf"]
def term (K : Complex (J := J) (O := O))
    (M : Modules K) (n : ℤ) :
    PresheafOfModules.{max u v} (ringSheaf J O).obj where
  obj U := ModuleCat.of ((ringSheaf J O).obj.obj U) (Family K M U n)
  map {U V} f := ModuleCat.semilinearMapAddEquiv ((ringSheaf J O).obj.map f).hom
    (ModuleCat.of ((ringSheaf J O).obj.obj U) (Family K M U n))
    (ModuleCat.of ((ringSheaf J O).obj.obj V) (Family K M V n))
    { toFun := fun x ↦
        DifferentialGradedModule.TensorProduct.mapLeftLinear M (restriction K f) n x
      map_add' := sorry
      map_smul' := sorry }
  map_id := sorry
  map_comp := sorry

/-- The relative tensor differential as a morphism of module presheaves. -/
@[stacks 09LV "relative tensor differential"]
def differential (K : Complex (J := J) (O := O))
    (M : Modules K) (n : ℤ) :
    term K M n ⟶ term K M (n + 1) where
  app U := ModuleCat.ofHom
    { toFun := DifferentialGradedModule.TensorProduct.differential M (sectionModule K U) n
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- Consecutive relative tensor differentials compose to zero as module-presheaf maps. -/
@[stacks 09LV "square-zero law for the relative tensor differential"]
theorem differential_comp (K : Complex (J := J) (O := O))
    (M : Modules K) (n : ℤ) :
    differential K M n ≫ differential K M (n + 1) = 0 := sorry

/-- The sectionwise relative tensor product as a cochain complex of module presheaves. -/
@[stacks 09LV "relative tensor presheaf complex"]
def presheafComplex (K : Complex (J := J) (O := O))
    (M : Modules K) :
    CochainComplex (PresheafOfModules.{max u v} (ringSheaf J O).obj) ℤ :=
  CochainComplex.of (term K M) (differential K M) (differential_comp K M)

/-- The sheafified sectionwise relative tensor product. -/
@[stacks 09LV "sheafified relative tensor complex"]
def obj (K : Complex (J := J) (O := O))
    (M : Modules K) : Complex (J := J) (O := O) :=
  ((moduleSheafification O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (presheafComplex K M)

/-- A homogeneous DG-module map induces a degree-shifting map of relative tensor terms. -/
@[stacks 09LV "homogeneous map on relative tensor terms"]
def termMap (K : Complex (J := J) (O := O))
    {M N : Modules K} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M N j) (n : ℤ) :
    term K M n ⟶ term K N (n + j) where
  app U := ModuleCat.ofHom
    { toFun := DifferentialGradedModule.TensorProduct.mapLinear (sectionModule K U) g n
      map_add' := sorry
      map_smul' := sorry }
  naturality := sorry

/-- The homogeneous map of sectionwise tensor terms assembled as a cochain of presheaves. -/
@[stacks 09LV "relative tensor presheaf map"]
def presheafMap (K : Complex (J := J) (O := O))
    {M N : Modules K} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M N j) :
    Cochain (presheafComplex K M) (presheafComplex K N) j :=
  Cochain.mk fun p _q hpq ↦ termMap K g p ≫ eqToHom (congrArg (term K N) hpq)

/-- Sheafification of the homogeneous relative tensor map. -/
@[stacks 09LV "sheafified relative tensor map"]
def map (K : Complex (J := J) (O := O))
    {M N : Modules K} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M N j) :
    Cochain (obj K M) (obj K N) j :=
  (presheafMap K g).map (moduleSheafification O)

/-- Lemma 22.35.1 (09LV) (1): for a complex `K` of modules on a ringed site, sectionwise relative
tensor product followed by module sheafification gives the DG functor
`- ⊗_(endDGA K) K`. -/
@[stacks 09LV "tensor with a complex over its endomorphism DGA"]
def tensorFunctor (K : Complex (J := J) (O := O)) :
    DgFunctor ℤ (Modules K) (Complex (J := J) (O := O)) where
  obj := obj K
  map := map K
  map_add := sorry
  map_smul := sorry
  map_d := sorry
  map_id := sorry
  map_comp := sorry

/-- Tensoring with `K` sends a right DG module to its explicitly sheafified sectionwise
relative tensor complex. -/
@[simp, stacks 09LV "object formula for tensoring with a complex"]
theorem tensorFunctor_obj (K : Complex (J := J) (O := O)) (M : Modules K) :
    (tensorFunctor K).obj M = obj K M := sorry

/-- The homogeneous map of tensoring with `K` is the sheafified sectionwise relative tensor
map. -/
@[simp, stacks 09LV "map formula for tensoring with a complex"]
theorem tensorFunctor_map (K : Complex (J := J) (O := O))
    {M N : Modules K} {j : ℤ}
    (g : DifferentialGradedModule.GradedHom (endDGA K) M N j) :
    (tensorFunctor K).map g = map K g := sorry

/-- The tensor-unit isomorphism on one open and in one degree, with its recovered
`O(U)`-linear structure. -/
@[stacks 09LV "sectionwise tensor-unit isomorphism"]
def regularTermIso (K : Complex (J := J) (O := O)) (U : Cᵒᵖ) (n : ℤ) :
    (term K (endDGA K).regularModule n).obj U ≅ (K.X n).val.obj U where
  hom := ModuleCat.ofHom
    { toFun := fun x ↦ ModuleCat.Hom.hom
        ((DifferentialGradedModule.TensorProduct.regularTensorIso
          (sectionModule K U)).hom.f n) x
      map_add' := sorry
      map_smul' := sorry }
  inv := ModuleCat.ofHom
    { toFun := fun x ↦ ModuleCat.Hom.hom
        ((DifferentialGradedModule.TensorProduct.regularTensorIso
          (sectionModule K U)).inv.f n) x
      map_add' := sorry
      map_smul' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The sectionwise tensor-unit isomorphism as an isomorphism of module presheaves. -/
@[stacks 09LV "presheaf tensor-unit isomorphism"]
def regularPresheafTermIso (K : Complex (J := J) (O := O)) (n : ℤ) :
    term K (endDGA K).regularModule n ≅ (K.X n).val :=
  PresheafOfModules.isoMk (fun U ↦ regularTermIso K U n) sorry

/-- Before sheafification, tensoring the regular module with `K` recovers the underlying
module-presheaf complex of `K`. -/
@[stacks 09LV "presheaf-level tensor-unit comparison"]
def regularPresheafIso (K : Complex (J := J) (O := O)) :
    presheafComplex K (endDGA K).regularModule ≅ underlyingComplex O K :=
  HomologicalComplex.Hom.isoOfComponents (regularPresheafTermIso K) sorry

/-- Degreewise module sheafification of the underlying presheaf complex recovers `K`. -/
@[stacks 09LV "sheafification bridge for the tensor unit"]
def sheafifiedUnderlyingIso (K : Complex (J := J) (O := O)) :
    ((moduleSheafification O).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (underlyingComplex O K) ≅ K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ moduleSheafificationValIso O (K.X n)) sorry

/-- Lemma 22.35.1 (09LV) (2): the tensor DG functor sends the regular endomorphism module to
the original complex `K`. -/
@[stacks 09LV "the regular endomorphism module maps to the original complex"]
def objRegularIso (K : Complex (J := J) (O := O)) :
    (tensorFunctor K).obj (endDGA K).regularModule ≅ K :=
  ((moduleSheafification O).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
      (regularPresheafIso K) ≪≫
    sheafifiedUnderlyingIso K

/-- Lemma 22.35.1 (09LV) (3): tensoring with `K` over its endomorphism DGA preserves arbitrary
direct sums. -/
@[stacks 09LV "tensor with a complex preserves arbitrary direct sums"]
instance preservesCoproducts (K : Complex (J := J) (O := O)) (ι : Type w) :
    PreservesColimitsOfShape (Discrete ι) (tensorFunctor K).mapComp := sorry

end SheafOfModules.RingedSite.TensorWithObject
