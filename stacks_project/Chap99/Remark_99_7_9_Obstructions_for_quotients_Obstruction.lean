module

public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Sheafification
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationAdjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import stacks_project.Chap66.Lemma_66_29_7_Quasicoherent
public import stacks_project.Chap67.Lemma_67_13_7_ProjectionFormula
public import stacks_project.Chap69.Lemma_69_13_2_IdealPower
public import stacks_project.Chap69.Lemma_69_17_2_Pullback
public import stacks_project.Chap99.Remark_99_7_9_Obstructions_for_quotients_Thickening
public import stacks_project.Chap99.«99_7_1_2_Functor»

/-!
# Canonical Ext¹ obstruction of a quotient point along a first-order thickening

Given `F` flat over `B` and a first-order thickening `T ⊂ T'` over `B`, a quotient
point `x` of `F_T` determines the mixed-scalar unit sequence of `F_{T'}` and, after
pullback along the kernel of `x` and pushout along the quotient, a canonical class
`o_x(T')` in `Ext¹_{O_{X_T}}(K, Q ⊗_{O_T} J)`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.Sheaf.InternalModule
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open RingedSite.ToposHom
open scoped TensorProduct

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The adjunction unit `F_{T'} ⟶ i_* F_T` of `fiberMap`, after identifying
`i^* F_{T'}` with `F_T`. -/
def unitToPushforward (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') :
    fiberF f F σ' ⟶
      (Modules.pushforward (fiberMap f h)).obj (fiberF f F σ) :=
  (Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app (fiberF f F σ') ≫
    (Modules.pushforward (fiberMap f h)).map (fiberFCompIso f F h).inv

/-- `unitToPushforward` is the adjunction unit followed by `i_*` of `fiberFCompIso.inv`. -/
theorem unitToPushforward_eq (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') :
    unitToPushforward f F h =
      (Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app (fiberF f F σ') ≫
        (Modules.pushforward (fiberMap f h)).map (fiberFCompIso f F h).inv :=
  sorry

/-- The kernel `i_*(i^* I ⊗ F_T)` of the mixed-scalar unit sequence, after the
76.9 identification of sheaves on `X_{T'}` with sheaves on `X_T`. This is not the
object equality `i_*(F_T ⊗ i^* I) = I ⊗ F_{T'}`. -/
def unitKernel (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    (fiber f σ').Modules :=
  (Modules.pushforward (fiberMap f h)).obj
    (tensorObj
      ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)))
      (fiberF f F σ))

/-- `unitKernel` is the pushforward of `i^* I ⊗ F_T`. -/
theorem unitKernel_eq (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    unitKernel f F h =
      (Modules.pushforward (fiberMap f h)).obj
        (tensorObj
          ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)))
          (fiberF f F σ)) :=
  sorry

/-- The domain of `Modules.action` of the ideal sheaf of `X_T ⊂ X_{T'}` on `F_{T'}`. -/
def idealTensor (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    (fiber f σ').Modules :=
  tensorObj (Hom.idealSheaf (fiberMap f h)) (fiberF f F σ')

/-- `idealTensor` is the algebraic-space tensor of `I` with `F_{T'}`. -/
theorem idealTensor_eq (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    idealTensor f F h =
      tensorObj (Hom.idealSheaf (fiberMap f h)) (fiberF f F σ') :=
  sorry

/-- The ideal-sheaf action `I ⊗ F_{T'} ⟶ F_{T'}` on the mixed-scalar side. -/
def idealTensor_to_fiberF (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    idealTensor f F h ⟶ fiberF f F σ' :=
  Modules.action (Hom.idealSheafSubobject (fiberMap f h)) (fiberF f F σ')

/-- `idealTensor_to_fiberF` is `Modules.action` of the ideal sheaf of `fiberMap`. -/
theorem idealTensor_to_fiberF_eq (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    idealTensor_to_fiberF f F h =
      Modules.action (Hom.idealSheafSubobject (fiberMap f h)) (fiberF f F σ') :=
  sorry

/-- Lemma 91.11.2 for `F_T` only: tensoring `idealComparison` with `F_T` is an
isomorphism. This is not claimed for a general quotient of `F_T`. -/
theorem isIso_tensorIdeal_comparison_fiberF (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    IsIso (tensorIdeal_comparison f h (fiberF f F σ)) :=
  sorry

/-- Named comparison of `i_*(i^* I ⊗ F_T)` into `unitKernel`; this is definitional
after the 76.9 pushforward presentation, not an object equality with `I ⊗ F_{T'}`. -/
def pushforwardIdealTensor_to_unitKernel (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    (Modules.pushforward (fiberMap f h)).obj
        (tensorObj
          ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)))
          (fiberF f F σ)) ⟶
      unitKernel f F h :=
  𝟙 _

/-- `pushforwardIdealTensor_to_unitKernel` is the identity on `unitKernel`. -/
theorem pushforwardIdealTensor_to_unitKernel_eq (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    pushforwardIdealTensor_to_unitKernel f F h = 𝟙 _ :=
  sorry

/-- The F-specific forward map `i_*(F_T ⊗ f_T^* J) ⟶ i_*(i^* I ⊗ F_T)` obtained from
the braiding `G ⊗ f_T^* J ⟶ f_T^* J ⊗ G`, the left-tensor of `idealComparison`, and
the named comparison into `unitKernel`. This is not claimed to be an isomorphism
for a general quotient of `F_T`. -/
def pushforwardFiberTensorIdeal_to_unitKernel (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)) ⟶
      unitKernel f F h :=
  (Modules.pushforward (fiberMap f h)).map
      (tensorIdeal_comparison f h (fiberF f F σ) ≫
        (Modules.ofCommModules (fiber f σ)).map
          (β_ ((Modules.toCommModules (fiber f σ)).obj (fiberF f F σ))
            ((Modules.toCommModules (fiber f σ)).obj
              ((Modules.pullback (fiberMap f h)).obj
                (Hom.idealSheaf (fiberMap f h))))).hom) ≫
    pushforwardIdealTensor_to_unitKernel f F h

/-- `pushforwardFiberTensorIdeal_to_unitKernel` is `i_*` of `tensorIdeal_comparison`
followed by the braiding into `i^* I ⊗ F_T`, then the named comparison into
`unitKernel`. -/
theorem pushforwardFiberTensorIdeal_to_unitKernel_eq (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    pushforwardFiberTensorIdeal_to_unitKernel f F h hF =
      (Modules.pushforward (fiberMap f h)).map
          (tensorIdeal_comparison f h (fiberF f F σ) ≫
            (Modules.ofCommModules (fiber f σ)).map
              (β_ ((Modules.toCommModules (fiber f σ)).obj (fiberF f F σ))
                ((Modules.toCommModules (fiber f σ)).obj
                  ((Modules.pullback (fiberMap f h)).obj
                    (Hom.idealSheaf (fiberMap f h))))).hom) ≫
        pushforwardIdealTensor_to_unitKernel f F h :=
  sorry

/-- Transport a morphism out of a commutative tensor product to `Y.Modules`. -/
def modulesTensorHom {Y : AlgebraicSpace S} {F G H : Y.Modules}
    (φ : (Modules.toCommModules Y).obj F ⊗ (Modules.toCommModules Y).obj G ⟶
      (Modules.toCommModules Y).obj H) :
    F ⊗ G ⟶ H :=
  (Modules.ofCommModules Y).map φ ≫ (Modules.commModulesEquivalence Y).counitIso.hom.app H

/-- `modulesTensorHom` is `ofCommModules` of the commutative tensor morphism, followed by
the counit of `commModulesEquivalence`. -/
theorem modulesTensorHom_eq {Y : AlgebraicSpace S} {F G H : Y.Modules}
    (φ : (Modules.toCommModules Y).obj F ⊗ (Modules.toCommModules Y).obj G ⟶
      (Modules.toCommModules Y).obj H) :
    modulesTensorHom φ =
      (Modules.ofCommModules Y).map φ ≫
        (Modules.commModulesEquivalence Y).counitIso.hom.app H :=
  sorry

/-- The type-valued sheaf underlying an `𝒪`-module. -/
abbrev moduleUnderlying {Y : AlgebraicSpace S} (M : Y.Modules) :
    Sheaf (smallEtaleTopology Y) (Type u) :=
  (ToInternal.underlying (structureSheaf Y)).obj M

/-- `moduleUnderlying` is the internal-module underlying type-valued sheaf. -/
theorem moduleUnderlying_eq {Y : AlgebraicSpace S} (M : Y.Modules) :
    moduleUnderlying M = (ToInternal.underlying (structureSheaf Y)).obj M :=
  sorry

/-- Pointwise pure tensor of commutative module sections. -/
def commPointwiseTensor {Y : AlgebraicSpace S} {A B : Modules.commModules Y}
    (U : (smallEtaleSite Y)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (PresheafOfModules.Monoidal.tensorObj A.val B.val).obj U :=
  x ⊗ₜ y

/-- `commPointwiseTensor` is the pointwise tensor product of commutative sections. -/
theorem commPointwiseTensor_eq {Y : AlgebraicSpace S} {A B : Modules.commModules Y}
    (U : (smallEtaleSite Y)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    commPointwiseTensor U x y =
      (x ⊗ₜ y : (PresheafOfModules.Monoidal.tensorObj A.val B.val).obj U) :=
  sorry

/-- Sheaf morphism from the sheafified pointwise tensor of `toComm F` and `toComm G`
to `toComm (F ⊗ G)`. -/
def commTensorComparison {Y : AlgebraicSpace S} (F G : Y.Modules) :
    (moduleSheafification.{u + 1, u, u, u}
      (commStructureSheaf Y)).obj
      (PresheafOfModules.Monoidal.tensorObj
        ((Modules.toCommModules Y).obj F).val
        ((Modules.toCommModules Y).obj G).val) ⟶
      (Modules.toCommModules Y).obj (F ⊗ G) :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u}
        (commStructureSheaf Y))
      ((Modules.toCommModules Y).obj F).val
      ((Modules.toCommModules Y).obj G).val).inv ≫
    tensorHom
      (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
        (commStructureSheaf Y) ((Modules.toCommModules Y).obj F)).hom
      (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
        (commStructureSheaf Y) ((Modules.toCommModules Y).obj G)).hom ≫
    (Modules.commModulesEquivalence Y).unit.app
      ((Modules.toCommModules Y).obj F ⊗ (Modules.toCommModules Y).obj G)

/-- `commTensorComparison` sheafifies the pointwise tensor and applies the unit of
`commModulesEquivalence`. -/
theorem commTensorComparison_eq {Y : AlgebraicSpace S} (F G : Y.Modules) :
    commTensorComparison F G =
      (Functor.Monoidal.μIso
          (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
          ((Modules.toCommModules Y).obj F).val
          ((Modules.toCommModules Y).obj G).val).inv ≫
        tensorHom
          (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
            (commStructureSheaf Y) ((Modules.toCommModules Y).obj F)).hom
          (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
            (commStructureSheaf Y) ((Modules.toCommModules Y).obj G)).hom ≫
        (Modules.commModulesEquivalence Y).unit.app
          ((Modules.toCommModules Y).obj F ⊗ (Modules.toCommModules Y).obj G) :=
  sorry

/-- Pure tensor of commutative presentations, transported to `toComm (M ⊗ N)`. -/
def commTensorSection {Y : AlgebraicSpace S} (M N : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ}
    (x : ((Modules.toCommModules Y).obj M).val.obj U)
    (y : ((Modules.toCommModules Y).obj N).val.obj U) :
    ((Modules.toCommModules Y).obj (M ⊗ N)).val.obj U :=
  (commTensorComparison M N).val.app U
    ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal.{u + 1, u, u, u}
        (commStructureSheaf Y)
        (PresheafOfModules.Monoidal.tensorObj
          ((Modules.toCommModules Y).obj M).val
          ((Modules.toCommModules Y).obj N).val)).app U
      (commPointwiseTensor U x y))

/-- `commTensorSection` applies `commTensorComparison` to a pointwise pure tensor. -/
theorem commTensorSection_eq {Y : AlgebraicSpace S} (M N : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ}
    (x : ((Modules.toCommModules Y).obj M).val.obj U)
    (y : ((Modules.toCommModules Y).obj N).val.obj U) :
    commTensorSection M N x y =
      (commTensorComparison M N).val.app U
        ((SheafOfModules.RingedSite.moduleSheafificationUnitToVal.{u + 1, u, u, u}
            (commStructureSheaf Y)
            (PresheafOfModules.Monoidal.tensorObj
              ((Modules.toCommModules Y).obj M).val
              ((Modules.toCommModules Y).obj N).val)).app U
          (commPointwiseTensor U x y)) :=
  sorry

/-- Restriction of scalars along `commRingSheafIso` does not change the section carrier. -/
theorem toCommModules_val_obj {Y : AlgebraicSpace S} (M : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    ((Modules.toCommModules Y).obj M).val.obj U = M.val.obj U :=
  sorry

/-- View a module section as a section of its commutative presentation. -/
def asCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    ((Modules.toCommModules Y).obj M).val.obj U :=
  eqToHom (toCommModules_val_obj M U).symm s

/-- `asCommSection` reidentifies a module section along `toCommModules_val_obj`. -/
theorem asCommSection_eq {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    asCommSection M s = eqToHom (toCommModules_val_obj M U).symm s :=
  sorry

/-- View a commutative presentation section as a section of the original module. -/
def ofCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : ((Modules.toCommModules Y).obj M).val.obj U) :
    M.val.obj U :=
  eqToHom (toCommModules_val_obj M U) s

/-- `ofCommSection` reidentifies a commutative section along `toCommModules_val_obj`. -/
theorem ofCommSection_eq {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : ((Modules.toCommModules Y).obj M).val.obj U) :
    ofCommSection M s = eqToHom (toCommModules_val_obj M U) s :=
  sorry

/-- The type-valued underlying sheaf has the same sections as the module sheaf. -/
theorem moduleUnderlying_obj {Y : AlgebraicSpace S} (M : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    (moduleUnderlying M).obj.obj U = M.val.obj U :=
  sorry

/-- Reidentify an underlying type-valued section as a module section. -/
def ofUnderlyingSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : (moduleUnderlying M).obj.obj U) :
    M.val.obj U :=
  eqToHom (moduleUnderlying_obj M U) s

/-- `ofUnderlyingSection` reidentifies along `moduleUnderlying_obj`. -/
theorem ofUnderlyingSection_eq {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : (moduleUnderlying M).obj.obj U) :
    ofUnderlyingSection M s = eqToHom (moduleUnderlying_obj M U) s :=
  sorry

/-- Reidentify a module section as an underlying type-valued section. -/
def toUnderlyingSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    (moduleUnderlying M).obj.obj U :=
  eqToHom (moduleUnderlying_obj M U).symm s

/-- `toUnderlyingSection` reidentifies along `moduleUnderlying_obj`. -/
theorem toUnderlyingSection_eq {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    toUnderlyingSection M s = eqToHom (moduleUnderlying_obj M U).symm s :=
  sorry

/-- The type-valued sheaf morphism sending a pair of local sections to their pure tensor. -/
def tensorSectionUnderlying {Z : AlgebraicSpace S} (M N : Z.Modules) :
    moduleUnderlying M ⊗ moduleUnderlying N ⟶ moduleUnderlying (M ⊗ N) where
  hom :=
    { app := fun U ↦
        TypeCat.ofHom fun p ↦
          toUnderlyingSection (M ⊗ N)
            (ofCommSection (M ⊗ N)
              (commTensorSection M N
                (asCommSection M
                  (ofUnderlyingSection M
                    ((fst (moduleUnderlying M) (moduleUnderlying N)).hom.app U p)))
                (asCommSection N
                  (ofUnderlyingSection N
                    ((snd (moduleUnderlying M) (moduleUnderlying N)).hom.app U p)))))
      naturality := fun _ _ _ ↦ sorry }

/-- `tensorSectionUnderlying` sends a pair of local sections to their pure tensor. -/
theorem tensorSectionUnderlying_eq {Z : AlgebraicSpace S} (M N : Z.Modules)
    (U : (smallEtaleSite Z)ᵒᵖ) (p : (moduleUnderlying M ⊗ moduleUnderlying N).obj.obj U) :
    (tensorSectionUnderlying M N).hom.app U p =
      toUnderlyingSection (M ⊗ N)
        (ofCommSection (M ⊗ N)
          (commTensorSection M N
            (asCommSection M
              (ofUnderlyingSection M
                ((fst (moduleUnderlying M) (moduleUnderlying N)).hom.app U p)))
            (asCommSection N
              (ofUnderlyingSection N
                ((snd (moduleUnderlying M) (moduleUnderlying N)).hom.app U p))))) :=
  sorry

/-- The cartesian type-valued comparison `h_* M × h_* N ⟶ h_*(M ⊗ N)`. -/
def pushforwardTensorUnderlying {Y Z : AlgebraicSpace S} (g : Z ⟶ Y)
    (M N : Z.Modules) :
    moduleUnderlying ((Modules.pushforward g).obj M) ⊗
      moduleUnderlying ((Modules.pushforward g).obj N) ⟶
      moduleUnderlying ((Modules.pushforward g).obj (M ⊗ N)) :=
  ((ModulePushforward.forgetIso (ringedToposHom g)).hom.app M ⊗ₘ
      (ModulePushforward.forgetIso (ringedToposHom g)).hom.app N) ≫
    typePushforward_prodLax g (moduleUnderlying M) (moduleUnderlying N) ≫
      (typePushforward g).map (tensorSectionUnderlying M N) ≫
        (ModulePushforward.forgetIso (ringedToposHom g)).inv.app (M ⊗ N)

/-- `pushforwardTensorUnderlying` is the type-valued pushforward product laxator
conjugated by `ModulePushforward.forgetIso`. -/
theorem pushforwardTensorUnderlying_eq {Y Z : AlgebraicSpace S} (g : Z ⟶ Y)
    (M N : Z.Modules) :
    pushforwardTensorUnderlying g M N =
      ((ModulePushforward.forgetIso (ringedToposHom g)).hom.app M ⊗ₘ
          (ModulePushforward.forgetIso (ringedToposHom g)).hom.app N) ≫
        typePushforward_prodLax g (moduleUnderlying M) (moduleUnderlying N) ≫
          (typePushforward g).map (tensorSectionUnderlying M N) ≫
            (ModulePushforward.forgetIso (ringedToposHom g)).inv.app (M ⊗ N) :=
  sorry

/-- Compatible bilinear map of commutative presentations representing the
pushforward tensorator. -/
def pushforwardTensorBilinear {Y Z : AlgebraicSpace S} (g : Z ⟶ Y)
    (M N : Z.Modules) :
    PresheafOfModules.BilinearMap (commStructureSheaf Y).obj
      ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj M)).val
      ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj N)).val
      ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj (M ⊗ N))).val where
  app U :=
    { toFun := fun x ↦
        { toFun := fun y ↦
            asCommSection ((Modules.pushforward g).obj (M ⊗ N))
              (ofUnderlyingSection ((Modules.pushforward g).obj (M ⊗ N))
                ((pushforwardTensorUnderlying g M N).hom.app U
                  (toUnderlyingSection ((Modules.pushforward g).obj M)
                    (ofCommSection _ x),
                    toUnderlyingSection ((Modules.pushforward g).obj N)
                      (ofCommSection _ y))))
          map_add' := fun _ _ ↦ sorry
          map_smul' := fun _ _ ↦ sorry }
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }
  naturality _ _ _ := sorry

/-- `pushforwardTensorBilinear` evaluates by pairing pushed-forward sections. -/
theorem pushforwardTensorBilinear_eq {Y Z : AlgebraicSpace S} (g : Z ⟶ Y)
    (M N : Z.Modules) (U : (smallEtaleSite Y)ᵒᵖ)
    (x : ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj M)).val.obj U)
    (y : ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj N)).val.obj U) :
    (pushforwardTensorBilinear g M N).app U x y =
      asCommSection ((Modules.pushforward g).obj (M ⊗ N))
        (ofUnderlyingSection ((Modules.pushforward g).obj (M ⊗ N))
          ((pushforwardTensorUnderlying g M N).hom.app U
            (toUnderlyingSection ((Modules.pushforward g).obj M) (ofCommSection _ x),
              toUnderlyingSection ((Modules.pushforward g).obj N)
                (ofCommSection _ y)))) :=
  sorry

/-- The lax comparison `(h_* M) ⊗ (h_* N) ⟶ h_*(M ⊗ N)`. -/
def pushforwardTensorLax {Y Z : AlgebraicSpace S} (g : Z ⟶ Y) (M N : Z.Modules) :
    (Modules.pushforward g).obj M ⊗ (Modules.pushforward g).obj N ⟶
      (Modules.pushforward g).obj (M ⊗ N) :=
  modulesTensorHom
    (tensorHom
        (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
          (commStructureSheaf Y)
          ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj M))).inv
        (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
          (commStructureSheaf Y)
          ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj N))).inv ≫
      Functor.LaxMonoidal.μ
        (moduleSheafification.{u + 1, u, u, u}
          (commStructureSheaf Y))
        ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj M)).val
        ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj N)).val ≫
      (moduleSheafification.{u + 1, u, u, u}
          (commStructureSheaf Y)).map
        (PresheafOfModules.BilinearMap.toHom (pushforwardTensorBilinear g M N)) ≫
      (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
        (commStructureSheaf Y)
        ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj (M ⊗ N)))).hom)

/-- `pushforwardTensorLax` is `modulesTensorHom` of the sheafified bilinear pairing. -/
theorem pushforwardTensorLax_eq {Y Z : AlgebraicSpace S} (g : Z ⟶ Y) (M N : Z.Modules) :
    pushforwardTensorLax g M N =
      modulesTensorHom
        (tensorHom
            (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
              (commStructureSheaf Y)
              ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj M))).inv
            (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
              (commStructureSheaf Y)
              ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj N))).inv ≫
          Functor.LaxMonoidal.μ
            (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
            ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj M)).val
            ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj N)).val ≫
          (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).map
            (PresheafOfModules.BilinearMap.toHom (pushforwardTensorBilinear g M N)) ≫
          (SheafOfModules.RingedSite.moduleSheafificationValIso.{u + 1, u, u, u}
            (commStructureSheaf Y)
            ((Modules.toCommModules Y).obj ((Modules.pushforward g).obj (M ⊗ N)))).hom) :=
  sorry

/-- The oplax comparison `i^*(I ⊗ F_{T'}) ⟶ i^* I ⊗ i^* F_{T'}`. This is a morphism,
not an object equality: module pullback is inverse image followed by extendScalars,
and `tensorObj` is the transported commutative tensor. -/
def pullbackIdealTensorComparison (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    (Modules.pullback (fiberMap f h)).obj (idealTensor f F h) ⟶
      tensorObj
        ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)))
        ((Modules.pullback (fiberMap f h)).obj (fiberF f F σ')) :=
  ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).homEquiv
      (idealTensor f F h)
      (tensorObj
        ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)))
        ((Modules.pullback (fiberMap f h)).obj (fiberF f F σ')))).symm
    (((Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app
          (Hom.idealSheaf (fiberMap f h)) ⊗ₘ
        (Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app
          (fiberF f F σ')) ≫
      pushforwardTensorLax (fiberMap f h)
        ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)))
        ((Modules.pullback (fiberMap f h)).obj (fiberF f F σ')))

/-- `pullbackIdealTensorComparison` is the adjunction transpose of the tensor of
units followed by `pushforwardTensorLax`. -/
theorem pullbackIdealTensorComparison_eq (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    pullbackIdealTensorComparison f F h =
      ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).homEquiv
          (idealTensor f F h)
          (tensorObj
            ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)))
            ((Modules.pullback (fiberMap f h)).obj (fiberF f F σ')))).symm
        (((Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app
              (Hom.idealSheaf (fiberMap f h)) ⊗ₘ
            (Modules.pullbackPushforwardAdjunction (fiberMap f h)).unit.app
              (fiberF f F σ')) ≫
          pushforwardTensorLax (fiberMap f h)
            ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h)))
            ((Modules.pullback (fiberMap f h)).obj (fiberF f F σ'))) :=
  sorry

/-- The oplax comparison `i^*(I ⊗ F_{T'}) ⟶ i^* I ⊗ i^* F_{T'}` is an isomorphism. -/
instance instIsIso_pullbackIdealTensorComparison (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left] :
    IsIso (pullbackIdealTensorComparison f F h) :=
  sorry

/-- Comparison `i^*(I ⊗ F_{T'}) ⟶ F_T ⊗ f_T^* J` from the oplax pullback-tensor
comparison, the inverse of `fiberFCompIso`, the braiding, and the inverse of
`tensorIdeal_comparison` for `F_T`. -/
def pulledIdealTensor_to_tensorIdeal (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    (Modules.pullback (fiberMap f h)).obj (idealTensor f F h) ⟶
      tensorIdeal f h (fiberF f F σ) :=
  pullbackIdealTensorComparison f F h ≫
    tensorHom (𝟙 _) (fiberFCompIso f F h).inv ≫
    (Modules.ofCommModules (fiber f σ)).map
      (β_
          ((Modules.toCommModules (fiber f σ)).obj
            ((Modules.pullback (fiberMap f h)).obj (Hom.idealSheaf (fiberMap f h))))
          ((Modules.toCommModules (fiber f σ)).obj (fiberF f F σ))).hom ≫
    @inv _ _ _ _ (tensorIdeal_comparison f h (fiberF f F σ))
      (isIso_tensorIdeal_comparison_fiberF f F h hF)

/-- `pulledIdealTensor_to_tensorIdeal` is the oplax comparison, inverse base-change,
braiding, and inverse of `tensorIdeal_comparison` for `F_T`. -/
theorem pulledIdealTensor_to_tensorIdeal_eq (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    pulledIdealTensor_to_tensorIdeal f F h hF =
      pullbackIdealTensorComparison f F h ≫
        tensorHom (𝟙 _) (fiberFCompIso f F h).inv ≫
        (Modules.ofCommModules (fiber f σ)).map
          (β_
              ((Modules.toCommModules (fiber f σ)).obj
                ((Modules.pullback (fiberMap f h)).obj
                  (Hom.idealSheaf (fiberMap f h))))
              ((Modules.toCommModules (fiber f σ)).obj (fiberF f F σ))).hom ≫
        @inv _ _ _ _ (tensorIdeal_comparison f h (fiberF f F σ))
          (isIso_tensorIdeal_comparison_fiberF f F h hF) :=
  sorry

/-- The adjunct `I ⊗ F_{T'} ⟶ i_*(F_T ⊗ f_T^* J)` of `pulledIdealTensor_to_tensorIdeal`. -/
def idealTensor_to_pushforwardTensorIdeal (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    idealTensor f F h ⟶
      (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)) :=
  (Modules.pullbackPushforwardAdjunction (fiberMap f h)).homEquiv _ _
    (pulledIdealTensor_to_tensorIdeal f F h hF)

/-- `idealTensor_to_pushforwardTensorIdeal` is the adjunction adjunct of
`pulledIdealTensor_to_tensorIdeal`. -/
theorem idealTensor_to_pushforwardTensorIdeal_eq (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    idealTensor_to_pushforwardTensorIdeal f F h hF =
      (Modules.pullbackPushforwardAdjunction (fiberMap f h)).homEquiv _ _
        (pulledIdealTensor_to_tensorIdeal f F h hF) :=
  sorry

/-- Lemma 91.11.2 for `F_T`: the comparison `I ⊗ F_{T'} ⟶ i_*(F_T ⊗ f_T^* J)` is an
isomorphism. This is not claimed for a general quotient of `F_T`. -/
instance instIsIso_idealTensor_to_pushforwardTensorIdeal (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    IsIso (idealTensor_to_pushforwardTensorIdeal f F h hF) :=
  sorry

/-- The adjunction counit is invertible on modules on `X_T` along the thickening
`X_T ⊂ X_{T'}`. -/
instance instIsIso_counit_fiberMap (f : X ⟶ B) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (G : (fiber f σ).Modules) :
    IsIso ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app G) :=
  sorry

/-- Inclusion `i_*(F_T ⊗ f_T^* J) ⟶ F_{T'}` from the braiding, `tensorIdeal_comparison`
for `F_T` only, and `Modules.action` of `Hom.idealSheafSubobject (fiberMap)` on
`F_{T'}`. -/
def unitInclusion (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    (Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)) ⟶
      fiberF f F σ' :=
  @inv _ _ _ _ (idealTensor_to_pushforwardTensorIdeal f F h hF)
      (instIsIso_idealTensor_to_pushforwardTensorIdeal f F h hF) ≫
    idealTensor_to_fiberF f F h

/-- `unitInclusion` is the inverse 91.11.2 comparison followed by the ideal-sheaf action. -/
theorem unitInclusion_eq (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    unitInclusion f F h hF =
      @inv _ _ _ _ (idealTensor_to_pushforwardTensorIdeal f F h hF)
          (instIsIso_idealTensor_to_pushforwardTensorIdeal f F h hF) ≫
        idealTensor_to_fiberF f F h :=
  sorry

/-- The action inclusion vanishes after `unitToPushforward`. -/
theorem unitInclusion_comp_unitToPushforward (f : X ⟶ B) (F : X.Modules)
    {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    unitInclusion f F h hF ≫ unitToPushforward f F h = 0 :=
  sorry

/-- The mixed-scalar deformation sequence
`0 → i_*(F_T ⊗ f_T^* J) → F_{T'} → i_* F_T → 0` on `X_{T'}`. The quotient map is
`unitToPushforward`, not the base-change isomorphism `fiberFCompIso`. -/
def unitExtension (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B} (h : σ ⟶ σ')
    [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    CategoryTheory.Extension
      ((Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)))
      ((Modules.pushforward (fiberMap f h)).obj (fiberF f F σ)) where
  E := fiberF f F σ'
  f := unitInclusion f F h hF
  g := unitToPushforward f F h
  zero := unitInclusion_comp_unitToPushforward f F h hF
  shortExact := sorry

/-- The kernel, middle, quotient, inclusion, and projection of `unitExtension`. -/
theorem unitExtension_spec (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) :
    (unitExtension f F h hF).E = fiberF f F σ' ∧
      (unitExtension f F h hF).f = unitInclusion f F h hF ∧
      (unitExtension f F h hF).g = unitToPushforward f F h :=
  sorry

/-- The short exact sequence `0 → K ⊗_{O_T} J → F_T ⊗_{O_T} J → Q ⊗_{O_T} J → 0`
obtained by tensoring `0 → K → F_T → Q → 0` with `f_T^* J`, using that `Q` is flat
over `T`. -/
def tensorKernelExtension (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') (Q : Point f F σ) :
    CategoryTheory.Extension (tensorIdeal f h (kernel Q.map))
      (tensorIdeal f h Q.module) where
  E := tensorIdeal f h (fiberF f F σ)
  f := tensorIdeal_map f h (kernel.ι Q.map)
  g := tensorIdeal_map f h Q.map
  zero := sorry
  shortExact := sorry

/-- `tensorKernelExtension` is the tensor of the kernel sequence of `Q` with `f_T^* J`. -/
theorem tensorKernelExtension_spec (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') (Q : Point f F σ) :
    (tensorKernelExtension f F h Q).E = tensorIdeal f h (fiberF f F σ) ∧
      (tensorKernelExtension f F h Q).f = tensorIdeal_map f h (kernel.ι Q.map) ∧
      (tensorKernelExtension f F h Q).g = tensorIdeal_map f h Q.map :=
  sorry

/-- The extension `0 → i_*(F_T ⊗_{O_T} J) → π⁻¹(i_* K) → i_* K → 0` obtained by
pulling `unitExtension` back along `i_*` of the kernel inclusion of `Q`. -/
def preimageExtension (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (Q : Point f F σ) :
    CategoryTheory.Extension
      ((Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h (fiberF f F σ)))
      ((Modules.pushforward (fiberMap f h)).obj (kernel Q.map)) :=
  CategoryTheory.Extension.pullback
    ((Modules.pushforward (fiberMap f h)).map (kernel.ι Q.map))
    (unitExtension f F h hF)

/-- `preimageExtension` is the pullback of `unitExtension` along `i_* (kernel.ι)`. -/
theorem preimageExtension_eq (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (Q : Point f F σ) :
    preimageExtension f F h hF Q =
      CategoryTheory.Extension.pullback
        ((Modules.pushforward (fiberMap f h)).map (kernel.ι Q.map))
        (unitExtension f F h hF) :=
  sorry

/-- The mixed-scalar pushout
`0 → i_*(Q ⊗_{O_T} J) → π⁻¹(i_* K)/i(i_*(K ⊗_{O_T} J)) → i_* K → 0` on `X_{T'}`. -/
def mixedCanonicalExtension (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (Q : Point f F σ) :
    CategoryTheory.Extension
      ((Modules.pushforward (fiberMap f h)).obj (tensorIdeal f h Q.module))
      ((Modules.pushforward (fiberMap f h)).obj (kernel Q.map)) :=
  CategoryTheory.Extension.pushout
    ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h Q.map))
    (preimageExtension f F h hF Q)

/-- `mixedCanonicalExtension` is the pushout of `preimageExtension` along
`i_* (tensorIdeal_map Q.map)`. -/
theorem mixedCanonicalExtension_eq (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (Q : Point f F σ) :
    mixedCanonicalExtension f F h hF Q =
      CategoryTheory.Extension.pushout
        ((Modules.pushforward (fiberMap f h)).map (tensorIdeal_map f h Q.map))
        (preimageExtension f F h hF Q) :=
  sorry

/-- The canonical extension
`0 → Q ⊗_{O_T} J → π⁻¹(K)/i(K ⊗_{O_T} J) → K → 0`
of `O_{X_T}`-modules, obtained by transporting `mixedCanonicalExtension` along
`i^*` and the adjunction counit. -/
def canonicalExtension (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (Q : Point f F σ) :
    CategoryTheory.Extension (tensorIdeal f h Q.module) (kernel Q.map) where
  E := (Modules.pullback (fiberMap f h)).obj (mixedCanonicalExtension f F h hF Q).E
  f := @inv _ _ _ _ ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
        (tensorIdeal f h Q.module)) (instIsIso_counit_fiberMap f h _) ≫
      (Modules.pullback (fiberMap f h)).map (mixedCanonicalExtension f F h hF Q).f
  g := (Modules.pullback (fiberMap f h)).map (mixedCanonicalExtension f F h hF Q).g ≫
      (Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app (kernel Q.map)
  zero := sorry
  shortExact := sorry

/-- `canonicalExtension` is `i^*` of `mixedCanonicalExtension`, transported by the
counit on the endpoints. -/
theorem canonicalExtension_spec (f : X ⟶ B) (F : X.Modules) {σ σ' : SchemesOver B}
    (h : σ ⟶ σ') [AlgebraicGeometry.IsFirstOrderThickening h.left.left]
    (hF : Modules.flatOver F f) (Q : Point f F σ) :
    (canonicalExtension f F h hF Q).E =
        (Modules.pullback (fiberMap f h)).obj
          (mixedCanonicalExtension f F h hF Q).E ∧
      (canonicalExtension f F h hF Q).f =
        @inv _ _ _ _ ((Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
            (tensorIdeal f h Q.module)) (instIsIso_counit_fiberMap f h _) ≫
          (Modules.pullback (fiberMap f h)).map
            (mixedCanonicalExtension f F h hF Q).f ∧
      (canonicalExtension f F h hF Q).g =
        (Modules.pullback (fiberMap f h)).map
            (mixedCanonicalExtension f F h hF Q).g ≫
          (Modules.pullbackPushforwardAdjunction (fiberMap f h)).counit.app
            (kernel Q.map) :=
  sorry

/-- A quotient point of `F_T` lifts to `Q_{F/X/B}(T')` when it is kernel-identified with
the pullback of a quotient point of `F_{T'}`. -/
def lifts {σ σ' : SchemesOver B} (h : σ ⟶ σ') {f : X ⟶ B} {F : X.Modules}
    (x : Point f F σ) : Prop :=
  ∃ x' : Point f F σ', Rel (x'.pullback h) x

/-- Lifting along `T ⊂ T'` is existence of a kernel-identified pullback. -/
theorem lifts_iff {σ σ' : SchemesOver B} (h : σ ⟶ σ') {f : X ⟶ B} {F : X.Modules}
    (x : Point f F σ) :
    lifts h x ↔ ∃ x' : Point f F σ', Rel (x'.pullback h) x :=
  sorry

/-- Lifts of kernel-identified quotient points correspond to the action of
`Q_{F/X/B}` on `T ⊂ T'`. -/
theorem lifts_iff_functor_map (f : X ⟶ B) (F : X.Modules) [F.IsQuasicoherent]
    {σ σ' : SchemesOver B} (h : σ ⟶ σ') (x : Point f F σ) :
    lifts h x ↔
      ∃ x' : Point f F σ',
        (functor f F).map (op h)
            (Quotient.mk (quotientSetoid f F σ') x') =
          Quotient.mk (quotientSetoid f F σ) x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
