module

public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SheafOfTypes
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.UnderlyingSheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Modules.InfinitesimalExtension

/-!
# Pushouts of infinitesimal extensions along morphisms of first-order thickenings

After identifying underlying spaces by the thickening homeomorphism, the middle sheaf of
the pushed-out infinitesimal extension is the abelian sheaf pushout of the transported inclusion
along the transported kernel comparison. The `𝒪_{X'₁}`-action is the unique descent of
the local-lift formula on the two pushout legs.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.ConcreteCategory CategoryTheory.Presheaf CategoryTheory.Presieve
open Opposite TopologicalSpace
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.RingedSpace.Modules
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X X1 X2 : RingedSpace.{u}} {i1 : X ⟶ X1}
variable [IsFirstOrderThickening i1]
variable {h : X1 ⟶ X2} [IsFirstOrderThickening (i1 ≫ h)]

/-- A morphism between two first-order thickenings of the same ringed space induces an
isomorphism of their underlying topological spaces. -/
def thickeningBaseIso (i1 : X ⟶ X1) [IsFirstOrderThickening i1]
    (h : X1 ⟶ X2) [IsFirstOrderThickening (i1 ≫ h)] : X1.carrier ≅ X2.carrier :=
  @asIso _ _ _ _ h.hom.base
    (IsIso.of_isIso_fac_left
      (show i1.hom.base ≫ h.hom.base = (i1 ≫ h).hom.base from rfl))

/-- Underlying abelian sheaves of `𝒪`-modules on a ringed space. -/
abbrev underlyingAbelian (Y : RingedSpace.{u}) :
    Y.Modules ⥤ Y.carrier.Sheaf AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf Y.ringCatSheaf

/-- Topological inverse image of abelian sheaves along the underlying continuous map of a
ringed-space morphism. For a morphism between first-order thickenings of the same ringed space,
this identifies abelian sheaves on the two homeomorphic spaces. -/
abbrev pullbackAlong (f : X1 ⟶ X2) :
    X2.carrier.Sheaf AddCommGrpCat.{u} ⥤ X1.carrier.Sheaf AddCommGrpCat.{u} :=
  TopCat.Sheaf.pullback AddCommGrpCat.{u} f.hom.base

/-- Open of `X'₂` corresponding to an open of `X'₁` under the homeomorphism `h`. -/
abbrev thickeningOpen (i1 : X ⟶ X1) [IsFirstOrderThickening i1]
    (h : X1 ⟶ X2) [IsFirstOrderThickening (i1 ≫ h)]
    (U : TopologicalSpace.Opens X1.carrier) : TopologicalSpace.Opens X2.carrier :=
  (TopologicalSpace.Opens.map (thickeningBaseIso i1 h).inv).obj U

/-- The middle term of an infinitesimal extension, as an abelian sheaf on `X'₁` after identifying
underlying spaces along the homeomorphism `h`. -/
def transportedModule {F K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    X1.carrier.Sheaf AddCommGrpCat.{u} :=
  (pullbackAlong h).obj ((underlyingAbelian X2).obj F'2.module)

/-- The transported inclusion `𝒦₂ ⟶ ℱ'₂` of underlying abelian sheaves. -/
def transportedι {F K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (pullbackAlong h).obj ((underlyingAbelian X2).obj (((i1 ≫ h) _*).obj K2)) ⟶
      transportedModule F'2 :=
  (pullbackAlong h).map ((underlyingAbelian X2).map F'2.ι)

/-- Comparison of `h_* (i₁_* M)` with the topological pushforward of the underlying
abelian sheaf of `i₁_* M`. -/
def toSheaf_pushforward (M : X1.Modules) :
    (underlyingAbelian X2).obj ((h _*).obj M) ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.hom.base).obj
        ((underlyingAbelian X1).obj M) :=
  𝟙 _

/-- Counit of the pullback-pushforward adjunction along `h.hom.base`. -/
def transportedCounit (M : X1.carrier.Sheaf AddCommGrpCat.{u}) :
    (pullbackAlong h).obj
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} h.hom.base).obj M) ⟶ M :=
  (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} h.hom.base).counit.app M

/-- The transported comparison `𝒦₂ ⟶ 𝒦₁` of underlying abelian sheaves on `X'₁`. -/
def transportedκ {K1 K2 : X.Modules} (κ : K2 ⟶ K1) :
    (pullbackAlong h).obj ((underlyingAbelian X2).obj (((i1 ≫ h) _*).obj K2)) ⟶
      (underlyingAbelian X1).obj ((i1 _*).obj K1) :=
  (pullbackAlong h).map ((underlyingAbelian X2).map (((i1 ≫ h) _*).map κ)) ≫
    (pullbackAlong h).map ((underlyingAbelian X2).map ((pushforwardCompIso i1 h).hom.app K1)) ≫
      (pullbackAlong h).map (toSheaf_pushforward ((i1 _*).obj K1)) ≫
        transportedCounit ((underlyingAbelian X1).obj ((i1 _*).obj K1))

/-- The projection from the transported middle term onto `i₁_* ℱ`, as abelian sheaves. -/
def transportedπ {F K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    transportedModule F'2 ⟶ (underlyingAbelian X1).obj ((i1 _*).obj F) :=
  (pullbackAlong h).map ((underlyingAbelian X2).map F'2.π) ≫
    (pullbackAlong h).map ((underlyingAbelian X2).map ((pushforwardCompIso i1 h).hom.app F)) ≫
      (pullbackAlong h).map (toSheaf_pushforward ((i1 _*).obj F)) ≫
        transportedCounit ((underlyingAbelian X1).obj ((i1 _*).obj F))

/-- The abelian sheaf pushout of the transported extension along `κ`. -/
def pushoutAbelian {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    X1.carrier.Sheaf AddCommGrpCat.{u} :=
  Limits.pushout (transportedι F'2) (transportedκ κ)

/-- The two legs of the transported extension square agree after projection to `i₁_* ℱ`. -/
theorem transported_desc_comm {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    transportedι F'2 ≫ transportedπ F'2 =
      transportedκ κ ≫ (0 : (underlyingAbelian X1).obj ((i1 _*).obj K1) ⟶
        (underlyingAbelian X1).obj ((i1 _*).obj F)) := sorry

/-- Projection of the abelian pushout onto `i₁_* ℱ`. -/
def pushoutAbelianπ {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    pushoutAbelian κ F'2 ⟶ (underlyingAbelian X1).obj ((i1 _*).obj F) :=
  Limits.pushout.desc (transportedπ F'2)
    (0 : (underlyingAbelian X1).obj ((i1 _*).obj K1) ⟶
      (underlyingAbelian X1).obj ((i1 _*).obj F))
    (transported_desc_comm κ F'2)

/-- The compatibility square of infinitesimal maps over `𝒪_X` associated to `κ : 𝒦₂ ⟶ 𝒦₁`. -/
def infinitesimalMapCommSq {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2)
    (κ : K2 ⟶ K1) : Prop :=
  CommSq (infinitesimalMap_restrict (i1 ≫ h) c2)
    (tensorHom (idealMapComp i1 h) (𝟙 F)) κ (infinitesimalMap_restrict i1 c1)

/-- The `c`-square is the commutativity of the restricted infinitesimal maps with `κ`. -/
theorem infinitesimalMapCommSq_iff {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    (c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2)
    (κ : K2 ⟶ K1) :
    infinitesimalMapCommSq c1 c2 κ ↔
      infinitesimalMap_restrict (i1 ≫ h) c2 ≫ κ =
        tensorHom (idealMapComp i1 h) (𝟙 F) ≫ infinitesimalMap_restrict i1 c1 := sorry

/-- The `ℱ'₂`-leg of the abelian pushout, as a map of abelian sheaves on `X'₁`. -/
def pushoutInlSheaf {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    transportedModule F'2 ⟶ pushoutAbelian κ F'2 :=
  Limits.pushout.inl (transportedι F'2) (transportedκ κ)

/-- The `𝒦₁`-leg of the abelian pushout, as a map of abelian sheaves on `X'₁`. -/
def pushoutInrSheaf {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (underlyingAbelian X1).obj ((i1 _*).obj K1) ⟶ pushoutAbelian κ F'2 :=
  Limits.pushout.inr (transportedι F'2) (transportedκ κ)

/-- `𝒪_{X'₁}` acts on `i₁_* 𝒦₁` through `i₁^♯`, then the result is included into the pushout. -/
def actionOnKernel {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (r : (X1.ringCatSheaf.obj).obj U)
    (x : ((i1 _*).obj K1).val.obj U) :
    (pushoutAbelian κ F'2).obj.obj U :=
  hom ((pushoutInrSheaf κ F'2).hom.app U)
    (hom (ModuleCat.smul (((i1 _*).obj K1).val.obj U) r) x)

/-- Equality identifying `h⁻¹(h(U))` with `U` along `thickeningBaseIso`. -/
theorem thickeningOpen_preimage_eq (i1 : X ⟶ X1) [IsFirstOrderThickening i1]
    (h : X1 ⟶ X2) [IsFirstOrderThickening (i1 ≫ h)]
    (U : TopologicalSpace.Opens X1.carrier) :
    (TopologicalSpace.Opens.map h.hom.base).obj (thickeningOpen i1 h U) = U :=
  ((congrArg (fun f ↦ (TopologicalSpace.Opens.map f).obj U)
      ((thickeningBaseIso i1 h).hom_inv_id)).trans
    (TopologicalSpace.Opens.map_id_obj U))

/-- `h^♯` as a morphism of sections of structure sheaves along the homeomorphism `h`. -/
def hSharpHom (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ) :
    (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop)) ⟶ (X1.sheaf.obj).obj U :=
  (h.hom.c).app (op (thickeningOpen i1 h U.unop)) ≫
    (X1.sheaf.obj).map (eqToHom (congrArg Opposite.op (thickeningOpen_preimage_eq i1 h U.unop)))

/-- `h^♯` applied to a section of `𝒪_{X'₂}` over the corresponding open, as a section of
`𝒪_{X'₁}`. -/
def hSharpSection (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (b : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop))) :
    (X1.sheaf.obj).obj U :=
  hom (hSharpHom U) b

/-- Difference `a - h^♯(b)` lies in `ker(i₁^♯)` exactly when `i₁^♯(a) = i₁^♯(h^♯(b))`. -/
theorem sub_mem_sectionIdeal_of_i1Sharp_eq (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U)
    (b : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop)))
    (hb : (commRingSheafPushforwardMap i1).hom.app U a =
      (commRingSheafPushforwardMap i1).hom.app U (hSharpSection U b)) :
    a - hSharpSection U b ∈
      KernelIdeal.sectionIdeal (commRingSheafPushforwardMap i1) U :=
  RingHom.mem_ker.mpr
    ((map_sub ((commRingSheafPushforwardMap i1).hom.app U).hom a (hSharpSection U b)).trans
      (sub_eq_zero.mpr hb))

/-- Kernel-ideal section of `a - h^♯(b)`, built from the compatibility `i₁^♯(a) = i₁^♯(h^♯(b))`
by the canonical sections isomorphism with `RingHom.ker`. -/
def idealSectionOfDifference (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U)
    (b : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop)))
    (hb : (commRingSheafPushforwardMap i1).hom.app U a =
      (commRingSheafPushforwardMap i1).hom.app U (hSharpSection U b)) :
    (kernelIdealSheaf i1).val.obj U :=
  hom (KernelIdeal.sectionsIso (commRingSheafPushforwardMap i1) U).inv
    ⟨a - hSharpSection U b, sub_mem_sectionIdeal_of_i1Sharp_eq U a b hb⟩

/-- The adjunction-unit identification of transported sections with sections of `ℱ'₂`
over the corresponding open. -/
def transportedSectionHom {F K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ) :
    ((underlyingAbelian X2).obj F'2.module).obj.obj (op (thickeningOpen i1 h U.unop)) ⟶
      (transportedModule F'2).obj.obj U :=
  ((TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} h.hom.base).unit.app
    ((underlyingAbelian X2).obj F'2.module)).hom.app (op (thickeningOpen i1 h U.unop)) ≫
    (transportedModule F'2).obj.map
      (eqToHom (congrArg Opposite.op (thickeningOpen_preimage_eq i1 h U.unop)))

/-- Image of an open of `X'₁` under an open embedding of the thickening homeomorphism
equals `thickeningOpen`. -/
theorem isOpenEmbedding_functor_obj_eq_thickeningOpen
    (i1 : X ⟶ X1) [IsFirstOrderThickening i1]
    (h : X1 ⟶ X2) [IsFirstOrderThickening (i1 ≫ h)]
    (hf : Topology.IsOpenEmbedding h.hom.base)
    (U : TopologicalSpace.Opens X1.carrier) :
    hf.functor.obj U = thickeningOpen i1 h U :=
  TopologicalSpace.Opens.ext
    (((TopCat.homeoOfIso (thickeningBaseIso i1 h)).image_eq_preimage_symm
        (U : Set X1.carrier)).trans
      (Eq.symm (TopologicalSpace.Opens.map_coe (thickeningBaseIso i1 h).inv U)))

/-- Inverse of `transportedSectionHom`, as the open-embedding sheaf pullback identification
along `thickeningBaseIso`, followed by the comparison of `h(U)` with `thickeningOpen U`. -/
def transportedSectionHomInv {F K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ) :
    (transportedModule F'2).obj.obj U ⟶
      ((underlyingAbelian X2).obj F'2.module).obj.obj (op (thickeningOpen i1 h U.unop)) :=
  let hf : Topology.IsOpenEmbedding h.hom.base :=
    (TopCat.homeoOfIso (thickeningBaseIso i1 h)).isOpenEmbedding
  let Fsheaf := (underlyingAbelian X2).obj F'2.module
  ((hf.sheafPullbackIso AddCommGrpCat.{u}).hom.app Fsheaf).hom.app U ≫
    Fsheaf.obj.map (eqToHom (congrArg Opposite.op
      (isOpenEmbedding_functor_obj_eq_thickeningOpen i1 h hf U.unop)))

/-- The identification of sections transported along the thickening homeomorphism is an
isomorphism. -/
theorem transportedSectionHom_isIso {F K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ) :
    IsIso (transportedSectionHom F'2 U) := sorry

/-- Actual action of a section of the second thickening on the transported
middle term, conjugated by the adjunction identification along `thickeningBaseIso`. -/
def transportedSMul {F K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (b : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop)))
    (s' : (transportedModule F'2).obj.obj U) :
    (transportedModule F'2).obj.obj U :=
  hom (transportedSectionHom F'2 U)
    (hom (ModuleCat.smul (F'2.module.val.obj (op (thickeningOpen i1 h U.unop))) b)
      (hom (transportedSectionHomInv F'2 U) s'))

/-- The `ℐ₁`-correction `c₁((a - h^♯(b)) ⊗ π(s'))` in `i₁_* 𝒦₁`. -/
def c1Correction {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U)
    (b : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop)))
    (hb : (commRingSheafPushforwardMap i1).hom.app U a =
      (commRingSheafPushforwardMap i1).hom.app U (hSharpSection U b))
    (s' : (transportedModule F'2).obj.obj U) :
    ((i1 _*).obj K1).val.obj U :=
  hom (c1.val.app U)
    (tensorSection X1.sheaf U (idealSectionOfDifference U a b hb)
      (hom ((transportedπ F'2).hom.app U) s'))

/-- Local action on a class from the middle term: act by the compatible lift
`b`, then add the actual kernel correction for `a - h^♯(b)`. -/
def actionOnClassFrom {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U)
    (b : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop)))
    (hb : (commRingSheafPushforwardMap i1).hom.app U a =
      (commRingSheafPushforwardMap i1).hom.app U (hSharpSection U b))
    (s' : (transportedModule F'2).obj.obj U) :
    (pushoutAbelian κ F'2).obj.obj U :=
  hom ((pushoutInlSheaf κ F'2).hom.app U) (transportedSMul F'2 U b s') +
    hom ((pushoutInrSheaf κ F'2).hom.app U) (c1Correction c1 F'2 U a b hb s')

/-- Two compatible local lifts give the same action. -/
theorem actionOnClassFrom_lift_independent {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ) (a : (X1.sheaf.obj).obj U)
    (b b' : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop)))
    (hb : (commRingSheafPushforwardMap i1).hom.app U a =
      (commRingSheafPushforwardMap i1).hom.app U (hSharpSection U b))
    (hb' : (commRingSheafPushforwardMap i1).hom.app U a =
      (commRingSheafPushforwardMap i1).hom.app U (hSharpSection U b'))
    (s' : (transportedModule F'2).obj.obj U) :
    actionOnClassFrom c1 κ F'2 U a b hb s' =
      actionOnClassFrom c1 κ F'2 U a b' hb' s' := sorry

/-- Pointwise biproduct of the transported middle term and `i₁_* 𝒦₁`, whose classes
generate the abelian pushout. -/
def generatorBiprod {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (TopologicalSpace.Opens X1.carrier)ᵒᵖ ⥤ AddCommGrpCat.{u} where
  obj U := (transportedModule F'2).obj.obj U ⊞
    ((underlyingAbelian X1).obj ((i1 _*).obj K1)).obj.obj U
  map f := biprod.map ((transportedModule F'2).obj.map f)
    (((underlyingAbelian X1).obj ((i1 _*).obj K1)).obj.map f)
  map_id _ := sorry
  map_comp _ _ := sorry

/-- The canonical map from generating pairs `(s', x)` to the abelian pushout. -/
def generatorBiprodToPushout {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    generatorBiprod κ F'2 ⟶ (pushoutAbelian κ F'2).obj where
  app U := biprod.desc ((pushoutInlSheaf κ F'2).hom.app U)
    ((pushoutInrSheaf κ F'2).hom.app U)
  naturality := sorry

/-- Classes of the abelian pushout are locally represented by pairs from the transported
middle term and `i₁_* 𝒦₁`. -/
theorem isLocallySurjective_generatorBiprodToPushout {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    IsLocallySurjective (Opens.grothendieckTopology X1.carrier)
      (generatorBiprodToPushout κ F'2) := sorry

/-- `(i1 ≫ h)^♯` as a map of presheaves on `X'₁`, after identifying underlying spaces
along the thickening homeomorphism. Defined as `i₁^♯ ∘ h^♯`, so the thickening
triangle is definitional on sections. -/
def transportedI2Sharp (i1 : X ⟶ X1) [IsFirstOrderThickening i1]
    (h : X1 ⟶ X2) [IsFirstOrderThickening (i1 ≫ h)] :
    ((Opens.map (thickeningBaseIso i1 h).inv).op ⋙ X2.presheaf) ⟶
      ((Opens.map i1.hom.base).op ⋙ X.presheaf) where
  app U :=
    (h.hom.c).app (op (thickeningOpen i1 h U.unop)) ≫
      (X1.sheaf.obj).map
        (eqToHom (congrArg Opposite.op (thickeningOpen_preimage_eq i1 h U.unop))) ≫
      (commRingSheafPushforwardMap i1).hom.app U
  naturality := sorry

/-- On sections, transported `(i1 ≫ h)^♯` is `i₁^♯ ∘ h^♯`. -/
theorem transportedI2Sharp_app_eq_i1Sharp_hSharp
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (b : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop))) :
    (transportedI2Sharp i1 h).app U b =
      (commRingSheafPushforwardMap i1).hom.app U (hSharpSection U b) :=
  (ConcreteCategory.comp_apply
      ((h.hom.c).app (op (thickeningOpen i1 h U.unop)) ≫
        (X1.sheaf.obj).map
          (eqToHom (congrArg Opposite.op (thickeningOpen_preimage_eq i1 h U.unop))))
      ((commRingSheafPushforwardMap i1).hom.app U) b).trans
    (congrArg ((commRingSheafPushforwardMap i1).hom.app U)
      (ConcreteCategory.comp_apply
        ((h.hom.c).app (op (thickeningOpen i1 h U.unop)))
        ((X1.sheaf.obj).map
          (eqToHom (congrArg Opposite.op (thickeningOpen_preimage_eq i1 h U.unop)))) b))

/-- Local surjectivity of `(i1 ≫ h)^♯` transports along the thickening homeomorphism. -/
theorem isLocallySurjective_transportedI2Sharp :
    IsLocallySurjective (Opens.grothendieckTopology X1.carrier)
      (transportedI2Sharp i1 h) := sorry

/-- The image of a section of `𝒪_{X'₁}` under `i₁^♯`, as a section of `i₁_* 𝒪_X`. -/
def i1SharpSection (i1 : X ⟶ X1) (U : (Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U) :
    ((Opens.map i1.hom.base).op ⋙ X.presheaf).obj U :=
  (commRingSheafPushforwardMap i1).hom.app U a

/-- The covering sieve on which `i₁^♯(a)` lifts through `(i1 ≫ h)^♯` and the pushout
class is represented by a pair from the transported middle term and `i₁_* 𝒦₁`. -/
def pushoutActionSieve {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U) (s : (pushoutAbelian κ F'2).obj.obj U) :
    Sieve U.unop :=
  imageSieve (transportedI2Sharp i1 h) (i1SharpSection i1 U a) ⊓
    imageSieve (generatorBiprodToPushout κ F'2) s

/-- The action sieve covers the open of `X'₁`. -/
theorem pushoutActionSieve_mem {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U) (s : (pushoutAbelian κ F'2).obj.obj U) :
    pushoutActionSieve κ F'2 U a s ∈
      Opens.grothendieckTopology X1.carrier U.unop := sorry

/-- A chosen local lift of `i₁^♯(a)` through `(i1 ≫ h)^♯` on an arrow of the action sieve. -/
def localCompatibleLift {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    {U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ}
    {V : TopologicalSpace.Opens X1.carrier} (g : V ⟶ U.unop)
    (a : (X1.sheaf.obj).obj U) (s : (pushoutAbelian κ F'2).obj.obj U)
    (hg : pushoutActionSieve κ F'2 U a s g) :
    (X2.sheaf.obj).obj (op (thickeningOpen i1 h V)) :=
  localPreimage (transportedI2Sharp i1 h) (i1SharpSection i1 U a) g hg.1

/-- The chosen local lift is compatible: `i₁^♯(a|_V) = i₁^♯(h^♯(b))`, obtained from
`app_localPreimage` of the action sieve, naturality of `i₁^♯`, and the thickening
triangle. -/
theorem localCompatibleLift_hb {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    {U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ}
    {V : TopologicalSpace.Opens X1.carrier} (g : V ⟶ U.unop)
    (a : (X1.sheaf.obj).obj U) (s : (pushoutAbelian κ F'2).obj.obj U)
    (hg : pushoutActionSieve κ F'2 U a s g) :
    (commRingSheafPushforwardMap i1).hom.app (op V)
        ((X1.sheaf.obj).map g.op a) =
      (commRingSheafPushforwardMap i1).hom.app (op V)
        (hSharpSection (op V) (localCompatibleLift κ F'2 g a s hg)) :=
  (NatTrans.naturality_apply (commRingSheafPushforwardMap i1).hom g.op a).trans
    ((app_localPreimage (transportedI2Sharp i1 h) (i1SharpSection i1 U a) g hg.1).symm.trans
      (transportedI2Sharp_app_eq_i1Sharp_hSharp (op V)
        (localCompatibleLift κ F'2 g a s hg)))

/-- Type-valued underlying presheaf of the abelian pushout. -/
abbrev pushoutAbelianType {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (TopologicalSpace.Opens X1.carrier)ᵒᵖ ⥤ Type u :=
  (pushoutAbelian κ F'2).obj ⋙ CategoryTheory.forget AddCommGrpCat.{u}

/-- The underlying abelian pushout is a type-valued sheaf, so compatible local action
families amalgamate. -/
theorem pushoutAbelian_isTypeSheaf {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    Presieve.IsSheaf (Opens.grothendieckTopology X1.carrier)
      (pushoutAbelianType κ F'2) := sorry

/-- Local action of `a` on a generating pair, using a lift of `i₁^♯(a)` through
`(i1 ≫ h)^♯`. -/
def actionOnGeneratingPair {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    {U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ}
    {V : TopologicalSpace.Opens X1.carrier} (g : V ⟶ U.unop)
    (a : (X1.sheaf.obj).obj U) (s : (pushoutAbelian κ F'2).obj.obj U)
    (hg : pushoutActionSieve κ F'2 U a s g) :
    (pushoutAbelian κ F'2).obj.obj (op V) :=
  let b := localCompatibleLift κ F'2 g a s hg
  let pair : (generatorBiprod κ F'2).obj (op V) :=
    localPreimage (generatorBiprodToPushout κ F'2) s g hg.2
  let s' := hom (biprod.fst : (generatorBiprod κ F'2).obj (op V) ⟶
      (transportedModule F'2).obj.obj (op V)) pair
  let x := hom (biprod.snd : (generatorBiprod κ F'2).obj (op V) ⟶
      ((underlyingAbelian X1).obj ((i1 _*).obj K1)).obj.obj (op V)) pair
  let aV := (X1.sheaf.obj).map g.op a
  let hb := localCompatibleLift_hb κ F'2 g a s hg
  let _ := hc
  actionOnClassFrom c1 κ F'2 (op V) aV b hb s' + actionOnKernel κ F'2 (op V) aV x

/-- The local action family on the covering sieve. -/
def actionFamily {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U) (s : (pushoutAbelian κ F'2).obj.obj U) :
    FamilyOfElements (pushoutAbelianType κ F'2)
      (pushoutActionSieve κ F'2 U a s).arrows :=
  fun _ g hg ↦ actionOnGeneratingPair c1 κ hc F'2 g a s hg

/-- Compatibility of the local action family; uses commutativity of the `c`-square and
square-zero to compare two lifts. -/
theorem actionFamily_compatible {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U) (s : (pushoutAbelian κ F'2).obj.obj U) :
    FamilyOfElements.Compatible (actionFamily c1 κ hc F'2 U a s) := sorry

/-- The transported inclusion `h^* (i₂_* 𝒦₂) ⟶ h^* ℱ'₂` of `𝒪_{X'₁}`-modules. -/
public def transportedιModule {F K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (h ^*).obj (((i1 ≫ h) _*).obj K2) ⟶ (h ^*).obj F'2.module :=
  (h ^*).map F'2.ι

/-- The comparison `h^* (i₂_* 𝒦₂) ⟶ i₁_* 𝒦₁` of `𝒪_{X'₁}`-modules induced by `κ`. -/
public def transportedκModule {K1 K2 : X.Modules} (κ : K2 ⟶ K1) :
    (h ^*).obj (((i1 ≫ h) _*).obj K2) ⟶ (i1 _*).obj K1 :=
  (h ^*).map (((i1 ≫ h) _*).map κ) ≫
    (h ^*).map ((pushforwardCompIso i1 h).hom.app K1) ≫
      (pullbackPushforwardAdjunction h).counit.app ((i1 _*).obj K1)

/-- Projection `h^* ℱ'₂ ⟶ i₁_* ℱ` of `𝒪_{X'₁}`-modules. -/
public def transportedπModule {F K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (h ^*).obj F'2.module ⟶ (i1 _*).obj F :=
  (h ^*).map F'2.π ≫
    (h ^*).map ((pushforwardCompIso i1 h).hom.app F) ≫
      (pullbackPushforwardAdjunction h).counit.app ((i1 _*).obj F)

/-- The two module legs agree after projection to `i₁_* ℱ`. -/
theorem transportedModule_desc_comm {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    transportedιModule F'2 ≫ transportedπModule F'2 =
      transportedκModule κ ≫ (0 : (i1 _*).obj K1 ⟶ (i1 _*).obj F) := sorry

/-- Objectwise `𝒪_{X'₁}`-action on the abelian pushout, amalgamating the local-lift
formula along the covering sieve supplied by local surjectivity of `(i1 ≫ h)^♯`.
The hypothesis `hc` is used so the action is independent of the choice of local
lifts and so the infinitesimal map of the resulting extension is `c₁`. -/
def pushoutSMul {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (a : (X1.sheaf.obj).obj U) (s : (pushoutAbelian κ F'2).obj.obj U) :
    (pushoutAbelian κ F'2).obj.obj U :=
  (pushoutAbelian_isTypeSheaf κ F'2 (pushoutActionSieve κ F'2 U a s)
      (pushoutActionSieve_mem κ F'2 U a s)).amalgamate
    (actionFamily c1 κ hc F'2 U a s)
    (actionFamily_compatible c1 κ hc F'2 U a s)

/-- The local `𝒪_{X'₁}`-module structure on sections of the abelian pushout. -/
@[reducible] def pushoutSectionModule {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ) :
    Module ((X1.ringCatSheaf.obj).obj U) ((pushoutAbelian κ F'2).obj.obj U) where
  smul := pushoutSMul c1 κ hc F'2 U
  one_smul := sorry
  mul_smul := sorry
  smul_zero := sorry
  smul_add := sorry
  add_smul := sorry
  zero_smul := sorry

/-- Restriction of the amalgamated local-lift action is semilinear over `𝒪_{X'₁}`. -/
theorem pushout_map_smul {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    {U V : (TopologicalSpace.Opens X1.carrier)ᵒᵖ} (f : U ⟶ V)
    (r : (X1.ringCatSheaf.obj).obj U) (m : (pushoutAbelian κ F'2).obj.obj U) :
    hom ((pushoutAbelian κ F'2).obj.map f) (pushoutSMul c1 κ hc F'2 U r m) =
      pushoutSMul c1 κ hc F'2 V (hom ((X1.ringCatSheaf.obj).map f) r)
        (hom ((pushoutAbelian κ F'2).obj.map f) m) := sorry

/-- The middle `𝒪_{X'₁}`-module is the abelian sheaf pushout of the transported
inclusion along the transported `κ`, equipped with the unique descent of the
local-lift action. This is not the module pullback `h^*`. -/
public def pushoutModule {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) : X1.Modules where
  val :=
    @PresheafOfModules.ofPresheaf (TopologicalSpace.Opens X1.carrier) _
      X1.ringCatSheaf.obj (pushoutAbelian κ F'2).obj
      (fun U ↦ pushoutSectionModule c1 κ hc F'2 U)
      (fun {_ _} f r m ↦ pushout_map_smul c1 κ hc F'2 f r m)
  isSheaf := (pushoutAbelian κ F'2).property

/-- The objectwise scalar action of the pushout module is the amalgamated local-lift
formula. -/
theorem pushoutSMul_eq_smul {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ)
    (r : (X1.ringCatSheaf.obj).obj U)
    (s : (pushoutModule c1 κ hc F'2).val.obj U) :
    pushoutSMul c1 κ hc F'2 U r s = r • s := sorry

/-- On an open with an explicit compatible scalar lift and an explicit pair
representative, the local-lift action plus the kernel correction is the two-leg
formula for the omitted `𝒪_{X'₁}`-action. -/
theorem actionOnClassFrom_add_kernel {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ) (a : (X1.sheaf.obj).obj U)
    (b : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop)))
    (hb : (commRingSheafPushforwardMap i1).hom.app U a =
      (commRingSheafPushforwardMap i1).hom.app U (hSharpSection U b))
    (s' : (transportedModule F'2).obj.obj U) (x : ((i1 _*).obj K1).val.obj U) :
    actionOnClassFrom c1 κ F'2 U a b hb s' + actionOnKernel κ F'2 U a x =
      hom ((pushoutInlSheaf κ F'2).hom.app U) (transportedSMul F'2 U b s') +
        hom ((pushoutInrSheaf κ F'2).hom.app U)
          (c1Correction c1 F'2 U a b hb s' +
            hom (ModuleCat.smul (((i1 _*).obj K1).val.obj U) a) x) := sorry

/-- The inclusion `i₁_* 𝒦₁ ⟶` the pushout module is the `𝒦₁`-leg of the abelian
pushout, as an `𝒪_{X'₁}`-linear map. -/
public def pushoutι {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (i1 _*).obj K1 ⟶ pushoutModule c1 κ hc F'2 where
  val := PresheafOfModules.homMk (pushoutInrSheaf κ F'2).hom sorry

/-- The projection from the pushout module onto `i₁_* ℱ` is the abelian pushout
description of the transported projection and the zero map on `𝒦₁`. -/
public def pushoutπ {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    pushoutModule c1 κ hc F'2 ⟶ (i1 _*).obj F where
  val := PresheafOfModules.homMk (pushoutAbelianπ κ F'2).hom sorry

/-- Forgetting the `𝒪_{X'₁}`-action recovers the abelian sheaf pushout of the
transported inclusion along the transported `κ`. -/
theorem pushoutModule_toSheaf {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (underlyingAbelian X1).obj (pushoutModule c1 κ hc F'2) = pushoutAbelian κ F'2 := sorry

/-- The inclusion of `i₁_* 𝒦₁` forgets to the `𝒦₁`-leg of the abelian pushout. -/
theorem pushoutι_toSheaf {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (underlyingAbelian X1).map (pushoutι c1 κ hc F'2) = pushoutInrSheaf κ F'2 := sorry

/-- The projection onto `i₁_* ℱ` forgets to the abelian pushout projection. -/
theorem pushoutπ_toSheaf {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    (underlyingAbelian X1).map (pushoutπ c1 κ hc F'2) = pushoutAbelianπ κ F'2 := sorry

/-- On a class coming from the transported middle term, the amalgamated action is
the local-lift formula. -/
theorem pushoutSMul_spec {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2)
    (U : (TopologicalSpace.Opens X1.carrier)ᵒᵖ) (a : (X1.sheaf.obj).obj U)
    (b : (X2.sheaf.obj).obj (op (thickeningOpen i1 h U.unop)))
    (hb : (commRingSheafPushforwardMap i1).hom.app U a =
      (commRingSheafPushforwardMap i1).hom.app U (hSharpSection U b))
    (s' : (transportedModule F'2).obj.obj U) :
    pushoutSMul c1 κ hc F'2 U a (hom ((pushoutInlSheaf κ F'2).hom.app U) s') =
      actionOnClassFrom c1 κ F'2 U a b hb s' := sorry

/-- The two legs of a morphism of extensions agree after transport to the abelian
pushout of the target. -/
theorem pushoutMapSheaf_comm {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) {F'2 G'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2}
    (φ : Hom F'2 G'2) :
    transportedι F'2 ≫
        ((pullbackAlong h).map ((underlyingAbelian X2).map φ.hom) ≫
          pushoutInlSheaf κ G'2) =
      transportedκ κ ≫ pushoutInrSheaf κ G'2 := sorry

/-- The abelian comparison of pushed-out middle terms induced by a morphism of
infinitesimal extensions. -/
public def pushoutMapSheaf {F K1 K2 : X.Modules}
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) {F'2 G'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2}
    (φ : Hom F'2 G'2) :
    pushoutAbelian κ F'2 ⟶ pushoutAbelian κ G'2 :=
  Limits.pushout.desc
    ((pullbackAlong h).map ((underlyingAbelian X2).map φ.hom) ≫
      pushoutInlSheaf κ G'2)
    (pushoutInrSheaf κ G'2) (pushoutMapSheaf_comm κ φ)

/-- The `𝒪_{X'₁}`-linear comparison of pushed-out middle terms induced by a
morphism of infinitesimal extensions. -/
public def pushoutMapHom {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    {F'2 G'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2} (φ : Hom F'2 G'2) :
    pushoutModule c1 κ hc F'2 ⟶ pushoutModule c1 κ hc G'2 where
  val := PresheafOfModules.homMk (pushoutMapSheaf κ φ).hom sorry

/-- Forgetting `𝒪_{X'₁}`-linearity recovers the abelian comparison of middle terms. -/
theorem pushoutMapHom_toSheaf {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    {F'2 G'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2} (φ : Hom F'2 G'2) :
    (underlyingAbelian X1).map (pushoutMapHom c1 κ hc φ) = pushoutMapSheaf κ φ := sorry

/-! The canonical pushout extension and its functoriality. -/

/-- Push an infinitesimal extension along a compatible morphism of kernel modules and a
morphism of first-order thickenings. The middle module has the underlying abelian sheaf
pushout and the scalar action descended from compatible local lifts. -/
def pushout {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    InfinitesimalExtension i1 F K1 c1 where
  module := pushoutModule c1 κ hc F'2
  ι := pushoutι c1 κ hc F'2
  π := pushoutπ c1 κ hc F'2
  w := sorry
  shortExact := sorry
  infMap_eq := sorry

/-- The canonical map from the transported middle abelian sheaf to the pushed-out middle
abelian sheaf. -/
def pushoutInl {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    transportedModule F'2 ⟶ pushoutAbelian κ F'2 :=
  let _ := c1
  let _ := hc
  pushoutInlSheaf κ F'2

/-- The transported inclusion and kernel comparison form a pushout square with the two
canonical maps into the pushed-out middle abelian sheaf. -/
theorem isPushout_pushout {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    IsPushout (transportedι F'2) (transportedκ κ)
      (pushoutInl c1 κ hc F'2) (pushoutInrSheaf κ F'2) := sorry

/-- A morphism of infinitesimal extensions gives maps on the transported middle sheaf and
kernel module that agree on their common domain in the abelian pushout. -/
theorem pushoutMap_desc_comm {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    {F'2 G'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2}
    (φ : Hom F'2 G'2) :
    transportedι F'2 ≫
        ((pullbackAlong h).map ((underlyingAbelian X2).map φ.hom) ≫
          pushoutInl c1 κ hc G'2) =
      transportedκ κ ≫ pushoutInrSheaf κ G'2 := sorry

/-- The morphism of pushed-out infinitesimal extensions induced by a morphism of the
original extensions, fixing the kernel and quotient. -/
def pushoutMap {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    {F'2 G'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2} (φ : Hom F'2 G'2) :
    Hom (pushout c1 κ hc F'2) (pushout c1 κ hc G'2) where
  hom := pushoutMapHom c1 κ hc φ
  comm_ι := sorry
  comm_π := sorry

/-- Pushout of infinitesimal extensions preserves identity morphisms. -/
theorem pushoutMap_id {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    pushoutMap c1 κ hc (Hom.id F'2) = Hom.id (pushout c1 κ hc F'2) := sorry

/-- Pushout of infinitesimal extensions preserves composition of morphisms. -/
theorem pushoutMap_comp {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    {F'2 G'2 H'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2}
    (φ : Hom F'2 G'2) (ψ : Hom G'2 H'2) :
    pushoutMap c1 κ hc (Hom.comp φ ψ) =
      Hom.comp (pushoutMap c1 κ hc φ) (pushoutMap c1 κ hc ψ) := sorry

/-- The infinitesimal map of the pushed-out extension equals the prescribed target map. -/
theorem pushout_infinitesimalMap {F K1 K2 : X.Modules}
    (c1 : kernelIdealSheaf i1 ⊗ (i1 _*).obj F ⟶ (i1 _*).obj K1)
    {c2 : kernelIdealSheaf (i1 ≫ h) ⊗ ((i1 ≫ h) _*).obj F ⟶ ((i1 ≫ h) _*).obj K2}
    (κ : K2 ⟶ K1) (hc : infinitesimalMapCommSq c1 c2 κ)
    (F'2 : InfinitesimalExtension (i1 ≫ h) F K2 c2) :
    infinitesimalMap i1 (pushout c1 κ hc F'2).ι (pushout c1 κ hc F'2).π
        (pushout c1 κ hc F'2).w (pushout c1 κ hc F'2).shortExact = c1 := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
