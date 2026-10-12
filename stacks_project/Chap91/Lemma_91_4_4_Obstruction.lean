/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flat.Generators
public import ReasLib.CategoryTheory.Abelian.Extension.Ext
public import stacks_project.Chap91.Remark_91_4_7_Extension

/-!
# Existence obstruction for 08L4 extensions

Along a first-order thickening, an `𝒪_X`-linear infinitesimal comparison
`c : ℐ ⊗ ℱ ⟶ 𝒦` determines a canonical class in `Ext ℱ 𝒦 2`.  Vanishing of this
class is equivalent to existence of an 08L4 sequence with infinitesimal map `c`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian (Ext)
open AlgebraicGeometry.RingedSpace
open AlgebraicGeometry.RingedSpace.Hom
open SheafOfModules.RingedSite.IdealSheaf
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules
namespace InfinitesimalExtension

variable {X X' : RingedSpace.{u}} (i : X ⟶ X') [IsFirstOrderThickening i]

/-- A chosen flat `𝒪_{X'}`-module covering `i _* ℱ`. -/
noncomputable def flatCover (F : X.Modules) : X'.Modules :=
  (exists_epi_from_flat ((i _*).obj F)).choose

/-- The chosen covering module is flat. -/
instance flatCover_isFlat (F : X.Modules) : (flatCover i F).IsFlat :=
  (exists_epi_from_flat ((i _*).obj F)).choose_spec.choose

/-- The chosen epimorphism from the flat cover onto `i _* ℱ`. -/
noncomputable def flatCover_π (F : X.Modules) : flatCover i F ⟶ (i _*).obj F :=
  (exists_epi_from_flat ((i _*).obj F)).choose_spec.choose_spec.choose

/-- The chosen covering morphism is an epimorphism. -/
instance flatCover_π_epi (F : X.Modules) : Epi (flatCover_π i F) :=
  (exists_epi_from_flat ((i _*).obj F)).choose_spec.choose_spec.choose_spec

/-- The chosen cover is a flat epimorphism onto `i _* ℱ`. -/
theorem flatCover_spec (F : X.Modules) :
    (flatCover i F).IsFlat ∧ Epi (flatCover_π i F) := sorry

/-- The kernel sequence `0 ⟶ 𝒥 ⟶ ℋ' ⟶ i _* ℱ ⟶ 0` of the chosen flat cover. -/
noncomputable def flatCoverKernelExtension (F : X.Modules) :
    Extension (kernel (flatCover_π i F)) ((i _*).obj F) where
  E := flatCover i F
  f := kernel.ι (flatCover_π i F)
  g := flatCover_π i F
  zero := kernel.condition _
  shortExact := sorry

/-- The kernel sequence of `flatCover_π` has middle object the chosen flat cover. -/
theorem flatCoverKernelExtension_spec (F : X.Modules) :
    (flatCoverKernelExtension i F).E = flatCover i F ∧
      (flatCoverKernelExtension i F).f = kernel.ι (flatCover_π i F) ∧
      (flatCoverKernelExtension i F).g = flatCover_π i F := sorry

/-- The comparison `ℐ ℋ' / ℐ 𝒥 ⟶ 𝒥 / ℐ 𝒥` of `𝒪_{X'}`-modules. -/
noncomputable def idealQuotientIncl (F : X.Modules) :
    cokernel ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F))) ⟶
      cokernel (action (kernelIdealSubobject i) (kernel (flatCover_π i F))) :=
  cokernel.desc
    ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F)))
    (kernel.lift (flatCover_π i F) (action (kernelIdealSubobject i) (flatCover i F))
        (action_comp_π i (0 : (i _*).obj F ⟶ flatCover i F) (flatCover_π i F)) ≫
      cokernel.π (action (kernelIdealSubobject i) (kernel (flatCover_π i F))))
    sorry

/-- After inverse image along `i`, the comparison `ℐ ℋ' / ℐ 𝒥 ⟶ 𝒥 / ℐ 𝒥` is a monomorphism
of `𝒪_X`-modules. -/
instance idealQuotientIncl_pullback_mono (F : X.Modules) :
    Mono ((i ^*).map (idealQuotientIncl i F)) := sorry

/-- The tensor of the kernel inclusion is annihilated by `ℐ ⊗ π ≫ c`. -/
theorem idealQuotientToKernel_comp_zero (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F)) ≫
      ((tensorLeft (kernelIdealSheaf i)).map (flatCover_π i F) ≫ c) = 0 := sorry

/-- The comparison `ℐ ℋ' / ℐ 𝒥 ⟶ i _* 𝒦` induced by `c`. -/
noncomputable def idealQuotientToKernel (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    cokernel ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F))) ⟶
      (i _*).obj K :=
  cokernel.desc
    ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F)))
    ((tensorLeft (kernelIdealSheaf i)).map (flatCover_π i F) ≫ c)
    (idealQuotientToKernel_comp_zero i F K c)

/-- `idealQuotientToKernel` is `c` after the tensor of the flat covering map. -/
theorem idealQuotientToKernel_spec (F K : X.Modules)
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    cokernel.π ((tensorLeft (kernelIdealSheaf i)).map (kernel.ι (flatCover_π i F))) ≫
        idealQuotientToKernel i F K c =
      (tensorLeft (kernelIdealSheaf i)).map (flatCover_π i F) ≫ c := sorry

variable (F K : X.Modules)

/-- An 08L4 extension of `ℱ` by an injective `𝒦` with infinitesimal map `c`, obtained by
pushing out the kernel sequence of a flat cover along the dotted lift supplied by injectivity. -/
noncomputable def ofInjective [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    InfinitesimalExtension i F K c :=
  let g : _ ⟶ K :=
    (i ^*).map (idealQuotientToKernel i F K c) ≫
      (pullbackPushforwardAdjunction i).counit.app K
  let f := (i ^*).map (idealQuotientIncl i F)
  let γ := Injective.factorThru g f
  let γ' :=
    cokernel.π (action (kernelIdealSubobject i) (kernel (flatCover_π i F))) ≫
      (pullbackPushforwardAdjunction i).unit.app
          (cokernel (action (kernelIdealSubobject i) (kernel (flatCover_π i F)))) ≫
        (i _*).map γ
  let S := Extension.pushout γ' (flatCoverKernelExtension i F)
  of S.E S.f S.g S.zero S.shortExact sorry

/-- The injective-case 08L4 extension is short exact with infinitesimal map `c`. -/
theorem ofInjective_spec [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (ShortComplex.mk (ofInjective i F K c).ι (ofInjective i F K c).π
        (ofInjective i F K c).w).ShortExact ∧
      infinitesimalMap i (ofInjective i F K c).ι (ofInjective i F K c).π
        (ofInjective i F K c).w (ofInjective i F K c).shortExact = c := sorry

/-- The infinitesimal map of `ofInjective` equals the prescribed `c`. -/
theorem ofInjective_infMap [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    infinitesimalMap i (ofInjective i F K c).ι (ofInjective i F K c).π
      (ofInjective i F K c).w (ofInjective i F K c).shortExact = c := sorry

/-- The injective presentation sequence `0 ⟶ 𝒦 ⟶ 𝒦' ⟶ 𝒬 ⟶ 0`. -/
noncomputable def injectiveCokernelExtension :
    Extension K (cokernel (HasFunctorialInjectives.ι.app K)) where
  E := HasFunctorialInjectives.obj K
  f := HasFunctorialInjectives.ι.app K
  g := cokernel.π (HasFunctorialInjectives.ι.app K)
  zero := cokernel.condition _
  shortExact := sorry

/-- `injectiveCokernelExtension` is the kernel-cokernel sequence of the chosen injective
embedding of `𝒦`. -/
theorem injectiveCokernelExtension_spec :
    (injectiveCokernelExtension K).E = HasFunctorialInjectives.obj K ∧
      (injectiveCokernelExtension K).f = HasFunctorialInjectives.ι.app K ∧
      (injectiveCokernelExtension K).g =
        cokernel.π (HasFunctorialInjectives.ι.app K) := sorry

/-- Pushout of the injective-case 08L4 envelope along `𝒦' ⟶ 𝒬`. -/
noncomputable def envelopePushoutExtension
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    Extension ((i _*).obj (cokernel (HasFunctorialInjectives.ι.app K))) ((i _*).obj F) :=
  let E' := ofInjective i F (HasFunctorialInjectives.obj K)
      (c ≫ (i _*).map (HasFunctorialInjectives.ι.app K))
  Extension.pushout ((i _*).map (cokernel.π (HasFunctorialInjectives.ι.app K)))
    { E := E'.module
      f := E'.ι
      g := E'.π
      zero := E'.w
      shortExact := E'.shortExact }

/-- `envelopePushoutExtension` is `Extension.pushout` of the injective-case envelope along
`i _*` of the cokernel projection of the chosen injective embedding. -/
theorem envelopePushoutExtension_eq
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    envelopePushoutExtension i F K c =
      Extension.pushout ((i _*).map (cokernel.π (HasFunctorialInjectives.ι.app K)))
        { E := (ofInjective i F (HasFunctorialInjectives.obj K)
              (c ≫ (i _*).map (HasFunctorialInjectives.ι.app K))).module
          f := (ofInjective i F (HasFunctorialInjectives.obj K)
              (c ≫ (i _*).map (HasFunctorialInjectives.ι.app K))).ι
          g := (ofInjective i F (HasFunctorialInjectives.obj K)
              (c ≫ (i _*).map (HasFunctorialInjectives.ι.app K))).π
          zero := (ofInjective i F (HasFunctorialInjectives.obj K)
              (c ≫ (i _*).map (HasFunctorialInjectives.ι.app K))).w
          shortExact := (ofInjective i F (HasFunctorialInjectives.obj K)
              (c ≫ (i _*).map (HasFunctorialInjectives.ι.app K))).shortExact } := sorry

/-- The descended `𝒪_X`-extension `0 ⟶ 𝒬 ⟶ 𝒟 ⟶ ℱ ⟶ 0` representing the `Ext¹` form of the
existence obstruction. -/
noncomputable def quotientObstructionExtension
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    Extension (cokernel (HasFunctorialInjectives.ι.app K)) F where
  E := (i ^*).obj (envelopePushoutExtension i F K c).E
  f := (asIso ((pullbackPushforwardAdjunction i).counit.app
          (cokernel (HasFunctorialInjectives.ι.app K)))).inv ≫
    (i ^*).map (envelopePushoutExtension i F K c).f
  g := (i ^*).map (envelopePushoutExtension i F K c).g ≫
    (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom
  zero := sorry
  shortExact := sorry

/-- The left and right maps of `quotientObstructionExtension` are the conjugates of
`envelopePushoutExtension` by the pullback-pushforward counit isomorphisms. -/
theorem quotientObstructionExtension_spec
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (quotientObstructionExtension i F K c).E =
        (i ^*).obj (envelopePushoutExtension i F K c).E ∧
      (quotientObstructionExtension i F K c).f =
        (asIso ((pullbackPushforwardAdjunction i).counit.app
            (cokernel (HasFunctorialInjectives.ι.app K)))).inv ≫
          (i ^*).map (envelopePushoutExtension i F K c).f ∧
      (quotientObstructionExtension i F K c).g =
        (i ^*).map (envelopePushoutExtension i F K c).g ≫
          (asIso ((pullbackPushforwardAdjunction i).counit.app F)).hom := sorry

variable [HasExt.{u} X.Modules]

/-- The existence obstruction `o(ℱ, 𝒦, c) ∈ Ext²_{𝒪_X}(ℱ, 𝒦)`. -/
noncomputable def existenceObstruction
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) : Ext F K 2 :=
  (quotientObstructionExtension i F K c).extClass.comp
    (injectiveCokernelExtension K).extClass (rfl : 1 + 1 = 2)

/-- `existenceObstruction` is the `Ext.comp` of the descended quotient class with the
injective-presentation class. -/
theorem existenceObstruction_eq
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    existenceObstruction i F K c =
      (quotientObstructionExtension i F K c).extClass.comp
        (injectiveCokernelExtension K).extClass (rfl : 1 + 1 = 2) := sorry

/-- The two `Ext¹` extensions whose composite is `existenceObstruction`. -/
theorem existenceObstruction_spec
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    (quotientObstructionExtension i F K c).E =
        (i ^*).obj (envelopePushoutExtension i F K c).E ∧
      (injectiveCokernelExtension K).E = HasFunctorialInjectives.obj K := sorry

/-- A splitting of the descended quotient extension, chosen from vanishing of the existence
obstruction. -/
theorem exists_section_of_eq_zero
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :
    ∃ s : F ⟶ (quotientObstructionExtension i F K c).E,
      s ≫ (quotientObstructionExtension i F K c).g = 𝟙 F := sorry

/-- An 08L4 extension reconstructed from vanishing of `o(ℱ, 𝒦, c)`, as the kernel of
`ℰ' ⟶ i _* (𝒟 / s(ℱ))`. -/
noncomputable def ofVanishing
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :
    InfinitesimalExtension i F K c :=
  let E' := ofInjective i F (HasFunctorialInjectives.obj K)
      (c ≫ (i _*).map (HasFunctorialInjectives.ι.app K))
  let s := (exists_section_of_eq_zero i F K c h).choose
  let φ :=
    pushout.inr ((i _*).map (cokernel.π (HasFunctorialInjectives.ι.app K))) E'.ι ≫
      (pullbackPushforwardAdjunction i).unit.app (envelopePushoutExtension i F K c).E ≫
        (i _*).map (cokernel.π s)
  of (kernel φ)
    (kernel.lift φ
      ((i _*).map (HasFunctorialInjectives.ι.app K) ≫ E'.ι) sorry)
    (kernel.ι φ ≫ E'.π) sorry sorry sorry

/-- The infinitesimal map of `ofVanishing` equals the prescribed `c`. -/
theorem ofVanishing_spec
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K)
    (h : existenceObstruction i F K c = 0) :
    infinitesimalMap i (ofVanishing i F K c h).ι (ofVanishing i F K c h).π
      (ofVanishing i F K c h).w (ofVanishing i F K c h).shortExact = c := sorry

/-- The existence obstruction vanishes when `𝒦` is injective. -/
theorem existenceObstruction_eq_zero_of_injective [Injective K]
    (c : kernelIdealSheaf i ⊗ (i _*).obj F ⟶ (i _*).obj K) :
    existenceObstruction i F K c = 0 := sorry

end InfinitesimalExtension
end AlgebraicGeometry.RingedSpace.Modules
