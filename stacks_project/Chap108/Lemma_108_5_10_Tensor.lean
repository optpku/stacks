/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Types.Basic
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Bilinear
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor.Sections
public import ReasLib.CategoryTheory.Monoidal.Invertible
public import stacks_project.Chap66.«66_26_0_1_Pushforward»
public import stacks_project.Chap67.Lemma_67_13_7_ProjectionFormula
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal
public import stacks_project.Chap99.«99_8_1_1_Functor»

/-!
# Tensor comparison for the Grothendieck Quot functor

Pointwise tensoring of Chap99 Quot-points with an invertible module, using the
adjunction transpose of the pushforward tensorator as the fibrewise comparison
`(F ⊗ L)_T ≅ F_T ⊗ L_T`. Chap71 `RelativeProj.pullbackTensorOplax` cannot be
imported with Chap99 `quot` because of the `schemeEtaleRingedHom` diamond, so
the same adjunction-transpose construction is rebuilt here from the Chap67
type-valued pushforward laxator and the Chap66 module adjunction.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open CategoryTheory.Sheaf.InternalModule
open RingedSite.ToposHom
open SheafOfModules.RingedSite


universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The tensor product of quasi-coherent `𝒪_X`-modules is quasi-coherent. -/
instance isQuasicoherent_tensorObj (F G : X.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (F ⊗ G).IsQuasicoherent :=
  sorry

/-- An invertible `𝒪_X`-module is quasi-coherent. -/
instance isQuasicoherent_of_isInvertible (L : X.Modules) [isInvertibleObject L] :
    L.IsQuasicoherent :=
  sorry

/-- Transport a morphism out of a commutative tensor product to `Y.Modules`. -/
def modulesTensorHom {Y : AlgebraicSpace S} {F G H : Y.Modules}
    (φ : (toCommModules Y).obj F ⊗ (toCommModules Y).obj G ⟶ (toCommModules Y).obj H) :
    F ⊗ G ⟶ H :=
  (ofCommModules Y).map φ ≫ (commModulesEquivalence Y).counitIso.hom.app H

/-- The type-valued sheaf underlying an `𝒪`-module. -/
abbrev moduleUnderlying {Y : AlgebraicSpace S} (M : Y.Modules) :
    Sheaf (smallEtaleTopology Y) (Type u) :=
  (ToInternal.underlying (structureSheaf Y)).obj M

/-- Pointwise pure tensor of commutative module sections. -/
def commPointwiseTensor {Y : AlgebraicSpace S} {A B : commModules Y}
    (U : (smallEtaleSite Y)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    (PresheafOfModules.Monoidal.tensorObj A.val B.val).obj U :=
  x ⊗ₜ y

/-- Sheaf morphism from the sheafified pointwise tensor of `toComm F` and `toComm G` to
`toComm (F ⊗ G)`. -/
def commTensorComparison {Y : AlgebraicSpace S} (F G : Y.Modules) :
    (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).obj
      (PresheafOfModules.Monoidal.tensorObj
        ((toCommModules Y).obj F).val
        ((toCommModules Y).obj G).val) ⟶
      (toCommModules Y).obj (F ⊗ G) :=
  (Functor.Monoidal.μIso
      (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
      ((toCommModules Y).obj F).val
      ((toCommModules Y).obj G).val).inv ≫
    tensorHom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((toCommModules Y).obj F)).hom
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((toCommModules Y).obj G)).hom ≫
    (commModulesEquivalence Y).unit.app
      ((toCommModules Y).obj F ⊗ (toCommModules Y).obj G)

/-- Pure tensor of commutative presentations, transported to `toComm (M ⊗ N)`. -/
def commTensorSection {Y : AlgebraicSpace S} (M N : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ}
    (x : ((toCommModules Y).obj M).val.obj U)
    (y : ((toCommModules Y).obj N).val.obj U) :
    ((toCommModules Y).obj (M ⊗ N)).val.obj U :=
  (commTensorComparison M N).val.app U
    ((moduleSheafificationUnitToVal.{u + 1, u, u, u} (commStructureSheaf Y)
        (PresheafOfModules.Monoidal.tensorObj
          ((toCommModules Y).obj M).val
          ((toCommModules Y).obj N).val)).app U
      (commPointwiseTensor U x y))

/-- Restriction of scalars along `commRingSheafIso` does not change the section carrier. -/
theorem toCommModules_val_obj {Y : AlgebraicSpace S} (M : Y.Modules)
    (U : (smallEtaleSite Y)ᵒᵖ) :
    ((toCommModules Y).obj M).val.obj U = M.val.obj U :=
  sorry

/-- View a module section as a section of its commutative presentation. -/
def asCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    ((toCommModules Y).obj M).val.obj U :=
  eqToHom (toCommModules_val_obj M U).symm s

/-- View a commutative presentation section as a section of the original module. -/
def ofCommSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : ((toCommModules Y).obj M).val.obj U) :
    M.val.obj U :=
  eqToHom (toCommModules_val_obj M U) s

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

/-- Reidentify a module section as an underlying type-valued section. -/
def toUnderlyingSection {Y : AlgebraicSpace S} (M : Y.Modules)
    {U : (smallEtaleSite Y)ᵒᵖ} (s : M.val.obj U) :
    (moduleUnderlying M).obj.obj U :=
  eqToHom (moduleUnderlying_obj M U).symm s

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

/-- The cartesian type-valued comparison `h_* M × h_* N ⟶ h_*(M ⊗ N)`. -/
def pushforwardTensorUnderlying {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M N : Z.Modules) :
    moduleUnderlying ((pushforward h).obj M) ⊗
      moduleUnderlying ((pushforward h).obj N) ⟶
      moduleUnderlying ((pushforward h).obj (M ⊗ N)) :=
  ((ModulePushforward.forgetIso (ringedToposHom h)).hom.app M ⊗ₘ
      (ModulePushforward.forgetIso (ringedToposHom h)).hom.app N) ≫
    typePushforward_prodLax h (moduleUnderlying M) (moduleUnderlying N) ≫
      (typePushforward h).map (tensorSectionUnderlying M N) ≫
        (ModulePushforward.forgetIso (ringedToposHom h)).inv.app (M ⊗ N)

/-- Compatible bilinear map of commutative presentations representing the
pushforward tensorator. -/
def pushforwardTensorBilinear {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (M N : Z.Modules) :
    PresheafOfModules.BilinearMap (commStructureSheaf Y).obj
      ((toCommModules Y).obj ((pushforward h).obj M)).val
      ((toCommModules Y).obj ((pushforward h).obj N)).val
      ((toCommModules Y).obj ((pushforward h).obj (M ⊗ N))).val where
  app U :=
    { toFun := fun x ↦
        { toFun := fun y ↦
            asCommSection ((pushforward h).obj (M ⊗ N))
              (ofUnderlyingSection ((pushforward h).obj (M ⊗ N))
                ((pushforwardTensorUnderlying h M N).hom.app U
                  (toUnderlyingSection ((pushforward h).obj M) (ofCommSection _ x),
                    toUnderlyingSection ((pushforward h).obj N) (ofCommSection _ y))))
          map_add' := fun _ _ ↦ sorry
          map_smul' := fun _ _ ↦ sorry }
      map_add' := fun _ _ ↦ sorry
      map_smul' := fun _ _ ↦ sorry }
  naturality _ _ _ := sorry

/-- The lax comparison `(h_* M) ⊗ (h_* N) ⟶ h_*(M ⊗ N)`, obtained by descending
the cartesian pairing of pushed-forward sections. -/
def pushforwardTensorLax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (M N : Z.Modules) :
    (pushforward h).obj M ⊗ (pushforward h).obj N ⟶
      (pushforward h).obj (M ⊗ N) :=
  modulesTensorHom
    (tensorHom
        (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
          ((toCommModules Y).obj ((pushforward h).obj M))).inv
        (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
          ((toCommModules Y).obj ((pushforward h).obj N))).inv ≫
      Functor.LaxMonoidal.μ
        (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y))
        ((toCommModules Y).obj ((pushforward h).obj M)).val
        ((toCommModules Y).obj ((pushforward h).obj N)).val ≫
      (moduleSheafification.{u + 1, u, u, u} (commStructureSheaf Y)).map
        (PresheafOfModules.BilinearMap.toHom (pushforwardTensorBilinear h M N)) ≫
      (moduleSheafificationValIso.{u + 1, u, u, u} (commStructureSheaf Y)
        ((toCommModules Y).obj ((pushforward h).obj (M ⊗ N)))).hom)

/-- The oplax comparison `h^*(A ⊗ B) ⟶ h^* A ⊗ h^* B`, the adjunction transpose of the
tensor of units followed by `pushforwardTensorLax`. -/
def pullbackTensorOplax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (pullback h).obj (A ⊗ B) ⟶ (pullback h).obj A ⊗ (pullback h).obj B :=
  ((pullbackPushforwardAdjunction h).homEquiv
      (A ⊗ B)
      ((pullback h).obj A ⊗ (pullback h).obj B)).symm
    (((pullbackPushforwardAdjunction h).unit.app A ⊗ₘ
        (pullbackPushforwardAdjunction h).unit.app B) ≫
      pushforwardTensorLax h ((pullback h).obj A) ((pullback h).obj B))

/-- The oplax pullback-tensor comparison is an isomorphism. -/
instance instIsIso_pullbackTensorOplax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y)
    (A B : Y.Modules) :
    IsIso (pullbackTensorOplax h A B) :=
  sorry

/-- The lax comparison `h^* A ⊗ h^* B ⟶ h^*(A ⊗ B)`, the inverse of
`pullbackTensorOplax`. -/
def pullbackTensorLax {Y Z : AlgebraicSpace S} (h : Z ⟶ Y) (A B : Y.Modules) :
    (pullback h).obj A ⊗ (pullback h).obj B ⟶ (pullback h).obj (A ⊗ B) :=
  inv (pullbackTensorOplax h A B)

end AlgebraicGeometry.AlgebraicSpace.Modules

namespace AlgebraicGeometry.AlgebraicSpace.Quot

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- The target module of a Chap99 Quot-point. -/
def QuotPoint.targetModule {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) : (fiber f σ).Modules :=
  Q.point.module

/-- The quotient morphism of a Chap99 Quot-point. -/
def QuotPoint.targetMap {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) :
    fiberF f F σ ⟶ Q.targetModule :=
  Q.point.map

/-- `QuotPoint.targetModule` is the module of the underlying Chap99 point. -/
theorem QuotPoint.targetModule_eq {f : X ⟶ B} {F : X.Modules}
    {σ : SchemesOver B} [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.targetModule = Q.point.module :=
  sorry

/-- `QuotPoint.targetMap` is the quotient morphism of the underlying Chap99
point. -/
theorem QuotPoint.targetMap_eq {f : X ⟶ B} {F : X.Modules} {σ : SchemesOver B}
    [FinitePresentation f] (Q : QuotPoint f F σ) :
    Q.targetMap = Q.point.map :=
  sorry

/-- Pullback of an invertible module along `X_T ⟶ X` remains invertible. -/
instance isInvertibleObject_fiberF (f : X ⟶ B) (L : X.Modules)
    [isInvertibleObject L] (σ : SchemesOver B) :
    isInvertibleObject (fiberF f L σ) :=
  sorry

/-- Pullback of modules along `X_T ⟶ X` identifies `(F ⊗ L)_T` with `F_T ⊗ L_T`,
as the Chap66 adjunction-transpose comparison. -/
def fiberTensorIso (f : X ⟶ B) (F L : X.Modules) (σ : SchemesOver B) :
    fiberF f (F ⊗ L) σ ≅ fiberF f F σ ⊗ fiberF f L σ where
  hom := Modules.pullbackTensorOplax (pullback.fst f σ.hom) F L
  inv := Modules.pullbackTensorLax (pullback.fst f σ.hom) F L
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward morphism of `fiberTensorIso` is the oplax pullback-tensor
comparison. -/
theorem fiberTensorIso_hom (f : X ⟶ B) (F L : X.Modules) (σ : SchemesOver B) :
    (fiberTensorIso f F L σ).hom =
      Modules.pullbackTensorOplax (pullback.fst f σ.hom) F L :=
  sorry

/-- The inverse morphism of `fiberTensorIso` is the lax pullback-tensor
comparison. -/
theorem fiberTensorIso_inv (f : X ⟶ B) (F L : X.Modules) (σ : SchemesOver B) :
    (fiberTensorIso f F L σ).inv =
      Modules.pullbackTensorLax (pullback.fst f σ.hom) F L :=
  sorry

/-- Tensoring a Quot-point `F_T ⟶ Q` with `L_T` yields a Quot-point of `F ⊗ L`. -/
def QuotPoint.tensor {f : X ⟶ B} [FinitePresentation f] {F : X.Modules}
    {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] : QuotPoint f (F ⊗ L) σ :=
  QuotPoint.ofEpi f (F ⊗ L) σ (Q.point.module ⊗ fiberF f L σ)
    ((fiberTensorIso f F L σ).hom ≫ (Q.point.map ⊗ₘ 𝟙 (fiberF f L σ)))
    sorry sorry sorry sorry sorry

/-- The underlying module of a tensored Quot-point is `Q ⊗ L_T`. -/
theorem QuotPoint.tensor_module {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] :
    (Q.tensor L).point.module = Q.point.module ⊗ fiberF f L σ :=
  sorry

/-- The quotient map of a tensored Quot-point is the pullback-tensor comparison
`(F ⊗ L)_T ≅ F_T ⊗ L_T` followed by `map ⊗ 𝟙`. -/
theorem QuotPoint.tensor_map {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] :
    (Q.tensor L).point.map =
      (fiberTensorIso f F L σ).hom ≫ (Q.point.map ⊗ₘ 𝟙 (fiberF f L σ)) :=
  sorry

/-- A tensored Quot-point is the epimorphism `(F ⊗ L)_T ⟶ Q ⊗ L_T` obtained by
tensoring `F_T ⟶ Q` with `L_T`. -/
theorem QuotPoint.tensor_spec {f : X ⟶ B} [FinitePresentation f]
    {F : X.Modules} {σ : SchemesOver B} (Q : QuotPoint f F σ) (L : X.Modules)
    [isInvertibleObject L] :
    (Q.tensor L).point.module = Q.point.module ⊗ fiberF f L σ ∧
      (Q.tensor L).point.map =
        (fiberTensorIso f F L σ).hom ≫ (Q.point.map ⊗ₘ 𝟙 (fiberF f L σ)) :=
  sorry

/-- Reassociation identifying `F` with `(F ⊗ L) ⊗ L⁻¹` before pullback. -/
def tensorInvReassoc (F L : X.Modules) [isInvertibleObject L] :
    F ⟶ (F ⊗ L) ⊗ isInvertibleObject.inverse L :=
  (ρ_ F).inv ≫
    (𝟙 F ⊗ₘ (isInvertibleObject.tensorInverseIso L).inv) ≫
    (α_ F L (isInvertibleObject.inverse L)).inv

/-- Tensoring a Quot-point of `F ⊗ L` with the pullback of `L⁻¹` recovers a
Quot-point of `F`. -/
def QuotPoint.tensorInv {f : X ⟶ B} [FinitePresentation f] (F L : X.Modules)
    {σ : SchemesOver B} [isInvertibleObject L]
    (Q : QuotPoint f (F ⊗ L) σ) : QuotPoint f F σ :=
  let Linv := isInvertibleObject.inverse L
  QuotPoint.ofEpi f F σ (Q.point.module ⊗ fiberF f Linv σ)
    ((Modules.pullback (pullback.fst f σ.hom)).map (tensorInvReassoc F L) ≫
      (fiberTensorIso f (F ⊗ L) Linv σ).hom ≫
        (Q.point.map ⊗ₘ 𝟙 (fiberF f Linv σ)))
    sorry sorry sorry sorry sorry

/-- The underlying module of `tensorInv` is `Q` tensored with the pullback of
`L⁻¹`. -/
theorem QuotPoint.tensorInv_module {f : X ⟶ B} [FinitePresentation f]
    (F L : X.Modules) {σ : SchemesOver B} [isInvertibleObject L]
    (Q : QuotPoint f (F ⊗ L) σ) :
    (QuotPoint.tensorInv F L Q).point.module =
      Q.point.module ⊗ fiberF f (isInvertibleObject.inverse L) σ :=
  sorry

/-- Kernel identification is preserved by tensoring Quot-points with `L_T`. -/
theorem tensor_rel (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [isInvertibleObject L] (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : QuotPoint f F σ),
      (quotSetoid f F σ).r Q₁ Q₂ →
        (quotSetoid f (F ⊗ L) σ).r (Q₁.tensor L) (Q₂.tensor L) :=
  sorry

/-- Kernel identification is preserved by the inverse tensor autoequivalence on
Quot-points. -/
theorem tensorInv_rel (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [isInvertibleObject L] (σ : SchemesOver B) :
    ∀ (Q₁ Q₂ : QuotPoint f (F ⊗ L) σ),
      (quotSetoid f (F ⊗ L) σ).r Q₁ Q₂ →
        (quotSetoid f F σ).r (QuotPoint.tensorInv F L Q₁)
          (QuotPoint.tensorInv F L Q₂) :=
  sorry

/-- The natural transformation `Quot_{F/X/B} ⟶ Quot_{F ⊗ L / X/B}` induced by
tensoring quotients with `L_T`. -/
def tensorHom (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] :
    quot f F ⟶ quot f (F ⊗ L) where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.tensor L)
        (tensor_rel f F L σ.unop))
  naturality := sorry

/-- The component of `tensorHom` at a test scheme is the setoid quotient map of
`QuotPoint.tensor`. -/
theorem tensorHom_app (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] (σ : (SchemesOver B)ᵒᵖ) :
    (tensorHom f F L).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f F σ.unop ↦ Q.tensor L)
          (tensor_rel f F L σ.unop)) :=
  sorry

/-- The inverse natural transformation `Quot_{F ⊗ L / X/B} ⟶ Quot_{F/X/B}`
induced by tensoring with the pullback of `L⁻¹`. -/
def tensorInvHom (f : X ⟶ B) [FinitePresentation f] (F L : X.Modules)
    [F.IsQuasicoherent] [isInvertibleObject L] :
    quot f (F ⊗ L) ⟶ quot f F where
  app σ :=
    TypeCat.ofHom
      (_root_.Quotient.map (fun Q : QuotPoint f (F ⊗ L) σ.unop ↦
          QuotPoint.tensorInv F L Q)
        (tensorInv_rel f F L σ.unop))
  naturality := sorry

/-- The component of `tensorInvHom` at a test scheme is the setoid quotient map
of `QuotPoint.tensorInv`. -/
theorem tensorInvHom_app (f : X ⟶ B) [FinitePresentation f]
    (F L : X.Modules) [F.IsQuasicoherent] [isInvertibleObject L]
    (σ : (SchemesOver B)ᵒᵖ) :
    (tensorInvHom f F L).app σ =
      TypeCat.ofHom
        (_root_.Quotient.map (fun Q : QuotPoint f (F ⊗ L) σ.unop ↦
            QuotPoint.tensorInv F L Q)
          (tensorInv_rel f F L σ.unop)) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Quot
