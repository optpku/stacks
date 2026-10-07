module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
public import stacks_project.Chap65.Lemma_65_7_3_Pullback
public import stacks_project.Chap66.Lemma_66_4_8_Opens
public import stacks_project.Chap66.Lemma_66_12_3
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_13_1_Correspondence
public import stacks_project.Chap67.Lemma_67_13_5_Complement
public import stacks_project.Chap70.Lemma_70_14_5_SectionsWithSupport
public import stacks_project.Chap71.Lemma_71_6_12_Pullback

/-!
# Strict transforms of modules and algebraic spaces

The strict transform of a module sheaf relative to a morphism `b : B' ⟶ B` and a
closed subspace `E ⊂ B'` is the quotient of the pullback to `X ×_B B'` by sections
supported on `|pr_{B'}^{-1} E|`. The strict transform of `X` is the closed subspace
of that fibre product cut out by the corresponding ideal of the structure sheaf.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- The structure sheaf of an algebraic space, viewed as a module over itself, is
quasi-coherent. -/
instance instIsQuasicoherent_structureSheaf (Y : AlgebraicSpace S) :
    (SheafOfModules.unit (structureSheaf Y) : Y.Modules).IsQuasicoherent :=
  sorry

variable {B B' X : AlgebraicSpace S}
variable (b : B' ⟶ B)

/-- The fibre-product ambient algebraic space `X ×_B B'` of a strict-transform
construction. -/
abbrev strictTransformAmbient (f : X ⟶ B) : AlgebraicSpace S :=
  pullback f b

/-- The ambient algebraic space is the fibre product of `f` and `b`. -/
theorem strictTransformAmbient_eq (f : X ⟶ B) :
    strictTransformAmbient b f = pullback f b :=
  sorry

/-- The closed subspace `pr_{B'}^{-1} E ⊂ X ×_B B'` obtained by pulling `E` back
along the second projection. -/
def strictTransformSupport (E : ClosedSubspace B') (f : X ⟶ B) :
    ClosedSubspace (strictTransformAmbient b f) :=
  E.inverseImage (pullback.snd f b)

/-- The inclusion of the pulled-back support is the inverse-image immersion of `E.ι`. -/
theorem strictTransformSupport_ι (E : ClosedSubspace B') (f : X ⟶ B) :
    (strictTransformSupport b E f).ι =
      inverseImageι (pullback.snd f b) E.ι :=
  sorry

/-- The pulled-back support is the inverse image of `E` along `pr_{B'}`. -/
theorem strictTransformSupport_spec (E : ClosedSubspace B') (f : X ⟶ B) :
    strictTransformSupport b E f = E.inverseImage (pullback.snd f b) :=
  sorry

/-- The open subspace of `X ×_B B'` complementary to `|pr_{B'}^{-1} E|`. -/
def strictTransformOpenComplement (E : ClosedSubspace B') (f : X ⟶ B) :
    OpenSubspace (strictTransformAmbient b f) :=
  closedImmersionComplementSubspace (strictTransformSupport b E f).ι

/-- The complementary open subspace is the open complement of the pulled-back support. -/
theorem strictTransformOpenComplement_eq (E : ClosedSubspace B') (f : X ⟶ B) :
    strictTransformOpenComplement b E f =
      closedImmersionComplementSubspace (strictTransformSupport b E f).ι :=
  sorry

/-- The underlying point-set of the complementary open subspace is the complement of
`|pr_{B'}^{-1} E|`. -/
theorem strictTransformOpenComplement_pointsSet (E : ClosedSubspace B')
    (f : X ⟶ B) :
    (strictTransformOpenComplement b E f).pointsSet =
      (strictTransformSupport b E f).pointsSetᶜ :=
  sorry

/-- The inclusion of the complementary open subspace is an open immersion. -/
instance instIsOpenImmersion_strictTransformOpenComplement_ι
    (E : ClosedSubspace B') (f : X ⟶ B) :
    IsOpenImmersion (strictTransformOpenComplement b E f).ι :=
  (strictTransformOpenComplement b E f).isOpenImmersion

/-- Pullback of module sheaves along `pr_X : X ×_B B' ⟶ X`. -/
abbrev strictTransformPullbackFunctor (f : X ⟶ B) :
    X.Modules ⥤ (strictTransformAmbient b f).Modules :=
  Modules.pullback (pullback.fst f b)

/-- Module pullback along `pr_X` is the small-étale module inverse image. -/
theorem strictTransformPullbackFunctor_eq (f : X ⟶ B) :
    strictTransformPullbackFunctor b f = Modules.pullback (pullback.fst f b) :=
  sorry

/-- The subsheaf of sections of an ambient module supported on `|pr_{B'}^{-1} E|`. -/
def strictTransformSupportedSubsheaf (E : ClosedSubspace B') (f : X ⟶ B)
    (G : (strictTransformAmbient b f).Modules) :
    (strictTransformAmbient b f).Modules :=
  Modules.sectionsWithSupportIn (strictTransformOpenComplement b E f).ι G

/-- The supported-section subsheaf is the kernel of restriction to the complementary
open subspace. -/
theorem strictTransformSupportedSubsheaf_eq (E : ClosedSubspace B') (f : X ⟶ B)
    (G : (strictTransformAmbient b f).Modules) :
    strictTransformSupportedSubsheaf b E f G =
      Modules.sectionsWithSupportIn (strictTransformOpenComplement b E f).ι G :=
  sorry

/-- The canonical inclusion of sections supported on `|pr_{B'}^{-1} E|`. -/
def strictTransformSupportedSubsheafι (E : ClosedSubspace B') (f : X ⟶ B)
    (G : (strictTransformAmbient b f).Modules) :
    strictTransformSupportedSubsheaf b E f G ⟶ G :=
  Modules.sectionsWithSupportInι (strictTransformOpenComplement b E f).ι G

/-- The supported-section inclusion is the kernel inclusion of restriction to the
complement. -/
theorem strictTransformSupportedSubsheafι_eq (E : ClosedSubspace B') (f : X ⟶ B)
    (G : (strictTransformAmbient b f).Modules) :
    strictTransformSupportedSubsheafι b E f G =
      Modules.sectionsWithSupportInι (strictTransformOpenComplement b E f).ι G :=
  sorry

/-- The supported-section inclusion is a monomorphism. -/
instance instMono_strictTransformSupportedSubsheafι (E : ClosedSubspace B')
    (f : X ⟶ B) (G : (strictTransformAmbient b f).Modules) :
    Mono (strictTransformSupportedSubsheafι b E f G) :=
  sorry

/-- Pullback followed by the functor of sections supported on `|pr_{B'}^{-1} E|`. -/
def strictTransformSupportedSectionsFunctor (E : ClosedSubspace B') (f : X ⟶ B) :
    X.Modules ⥤ (strictTransformAmbient b f).Modules :=
  strictTransformPullbackFunctor b f ⋙
    Modules.sectionsWithSupportFunctor (strictTransformOpenComplement b E f).ι

/-- The supported-section functor is pullback composed with the closed-support kernel
functor. -/
theorem strictTransformSupportedSectionsFunctor_eq (E : ClosedSubspace B')
    (f : X ⟶ B) :
    strictTransformSupportedSectionsFunctor b E f =
      strictTransformPullbackFunctor b f ⋙
        Modules.sectionsWithSupportFunctor
          (strictTransformOpenComplement b E f).ι :=
  sorry

/-- The natural inclusion of supported sections into the pulled-back module sheaf. -/
def strictTransformSupportedSectionsInclusion (E : ClosedSubspace B')
    (f : X ⟶ B) :
    strictTransformSupportedSectionsFunctor b E f ⟶
      strictTransformPullbackFunctor b f :=
  Functor.whiskerLeft (strictTransformPullbackFunctor b f)
      (kernel.ι (Modules.pullbackPushforwardAdjunction
        (strictTransformOpenComplement b E f).ι).unit) ≫
    (Functor.rightUnitor (strictTransformPullbackFunctor b f)).hom

/-- The component of the supported-section inclusion at `F` is the kernel inclusion of
sections of `pr_X^* F` supported on `|pr_{B'}^{-1} E|`. -/
theorem strictTransformSupportedSectionsInclusion_app (E : ClosedSubspace B')
    (f : X ⟶ B) (F : X.Modules) :
    (strictTransformSupportedSectionsInclusion b E f).app F =
      strictTransformSupportedSubsheafι b E f
        ((strictTransformPullbackFunctor b f).obj F) :=
  sorry

/-- The strict-transform functor is the functor-category cokernel of the natural
inclusion of supported sections into pullback. -/
def strictTransformFunctor (E : ClosedSubspace B') (f : X ⟶ B) :
    X.Modules ⥤ (strictTransformAmbient b f).Modules :=
  cokernel (strictTransformSupportedSectionsInclusion b E f)

/-- The strict-transform functor is the cokernel of the supported-section inclusion. -/
theorem strictTransformFunctor_eq (E : ClosedSubspace B') (f : X ⟶ B) :
    strictTransformFunctor b E f =
      cokernel (strictTransformSupportedSectionsInclusion b E f) :=
  sorry

/-- The strict transform of a module sheaf is its pullback to `X ×_B B'` modulo
sections supported on `|pr_{B'}^{-1} E|`. -/
abbrev strictTransformModule (E : ClosedSubspace B') (f : X ⟶ B) (F : X.Modules) :
    (strictTransformAmbient b f).Modules :=
  (strictTransformFunctor b E f).obj F

/-- The strict transform of `F` is the value of the strict-transform functor. -/
theorem strictTransformModule_eq (E : ClosedSubspace B') (f : X ⟶ B)
    (F : X.Modules) :
    strictTransformModule b E f F = (strictTransformFunctor b E f).obj F :=
  sorry

/-- The strict transform of `F` is canonically isomorphic to the objectwise cokernel of
the supported-section inclusion of `pr_X^* F`. -/
def strictTransformModuleIsoCokernel (E : ClosedSubspace B') (f : X ⟶ B)
    (F : X.Modules) :
    strictTransformModule b E f F ≅
      cokernel ((strictTransformSupportedSectionsInclusion b E f).app F) :=
  PreservesCokernel.iso
    ((evaluation X.Modules (strictTransformAmbient b f).Modules).obj F)
    (strictTransformSupportedSectionsInclusion b E f)

/-- The canonical natural quotient map from pullback to the strict-transform functor. -/
def strictTransformπNat (E : ClosedSubspace B') (f : X ⟶ B) :
    strictTransformPullbackFunctor b f ⟶ strictTransformFunctor b E f :=
  cokernel.π (strictTransformSupportedSectionsInclusion b E f)

/-- The natural quotient map is the cokernel projection of the supported-section
inclusion. -/
theorem strictTransformπNat_eq (E : ClosedSubspace B') (f : X ⟶ B) :
    strictTransformπNat b E f =
      cokernel.π (strictTransformSupportedSectionsInclusion b E f) :=
  sorry

/-- The canonical quotient map `pr_X^* F ⟶ F'` onto the strict transform. -/
abbrev strictTransformπ (E : ClosedSubspace B') (f : X ⟶ B) (F : X.Modules) :
    (strictTransformPullbackFunctor b f).obj F ⟶
      strictTransformModule b E f F :=
  (strictTransformπNat b E f).app F

/-- The quotient map is the component of the cokernel projection. -/
theorem strictTransformπ_eq (E : ClosedSubspace B') (f : X ⟶ B) (F : X.Modules) :
    strictTransformπ b E f F = (strictTransformπNat b E f).app F :=
  sorry

/-- The objectwise cokernel projection is the strict-transform quotient followed by the
evaluation comparison. -/
theorem strictTransformModuleIsoCokernel_hom (E : ClosedSubspace B') (f : X ⟶ B)
    (F : X.Modules) :
    strictTransformπ b E f F ≫ (strictTransformModuleIsoCokernel b E f F).hom =
      cokernel.π ((strictTransformSupportedSectionsInclusion b E f).app F) :=
  sorry

/-- If the complementary open immersion is quasi-compact, sections of a quasi-coherent
ambient module supported on `|pr_{B'}^{-1} E|` form a quasi-coherent subsheaf. -/
instance instIsQuasicoherent_strictTransformSupportedSubsheaf
    (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι]
    (G : (strictTransformAmbient b f).Modules) [G.IsQuasicoherent] :
    (strictTransformSupportedSubsheaf b E f G).IsQuasicoherent :=
  Modules.sectionsWithSupportIn_isQuasicoherent
    (strictTransformOpenComplement b E f).ι G

/-- If the complementary open immersion is quasi-compact, the strict transform of a
quasi-coherent module is quasi-coherent. -/
instance instIsQuasicoherent_strictTransformModule (E : ClosedSubspace B')
    (f : X ⟶ B) (F : X.Modules)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] [F.IsQuasicoherent] :
    (strictTransformModule b E f F).IsQuasicoherent :=
  sorry

/-- The ideal of structure-sheaf sections supported on `|pr_{B'}^{-1} E|`. -/
def strictTransformIdeal (E : ClosedSubspace B') (f : X ⟶ B) :
    IdealSubobject (strictTransformAmbient b f) :=
  Subobject.mk (strictTransformSupportedSubsheafι b E f
    (SheafOfModules.unit (structureSheaf (strictTransformAmbient b f))))

/-- The strict-transform ideal is the subobject of supported structure-sheaf sections. -/
theorem strictTransformIdeal_eq (E : ClosedSubspace B') (f : X ⟶ B) :
    strictTransformIdeal b E f =
      Subobject.mk (strictTransformSupportedSubsheafι b E f
        (SheafOfModules.unit (structureSheaf (strictTransformAmbient b f)))) :=
  sorry

/-- If the complementary open immersion is quasi-compact, the strict-transform ideal
is a quasi-coherent ideal sheaf. -/
instance instIsQuasiCoherent_strictTransformIdeal (E : ClosedSubspace B')
    (f : X ⟶ B) [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    IsQuasiCoherent (strictTransformIdeal b E f) :=
  sorry

/-- The strict transform of `X` is the closed subspace of `X ×_B B'` cut out by the
quasi-coherent ideal of structure-sheaf sections supported on `|pr_{B'}^{-1} E|`. -/
def strictTransform (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    ClosedSubspace (strictTransformAmbient b f) :=
  ClosedSubspace.ofQuasiCoherentIdeal (strictTransformIdeal b E f)

/-- The inclusion of the strict transform is the closed immersion cut out by the
supported-section ideal. -/
theorem strictTransform_ι (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    (strictTransform b E f).ι = subschemeι (strictTransformIdeal b E f) :=
  sorry

/-- The strict transform is the closed subspace associated to the supported-section
ideal of `𝒪_{X ×_B B'}`. -/
theorem strictTransform_spec (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    strictTransform b E f =
      ClosedSubspace.ofQuasiCoherentIdeal (strictTransformIdeal b E f) :=
  sorry

/-- The ideal sheaf of the strict transform is the supported-section ideal. -/
theorem strictTransform_idealSheaf (E : ClosedSubspace B') (f : X ⟶ B)
    [QuasiCompact (strictTransformOpenComplement b E f).ι] :
    (strictTransform b E f).idealSheaf = strictTransformIdeal b E f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
