module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChangeOfBase.Identity
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoids.Evaluation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Symmetry.Swap
public import ReasLib.CategoryTheory.Fibered.Groupoids.Diagonal.Construction

/-! # Kernel-pair groupoids in algebraic spaces -/

@[expose] public section

-- Public constructions retain their private coordinate data in their explicit bodies.
set_option backward.privateInPublic true
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits Bicategory
open FiberedCategoryOver.Groupoids BasedNatIso
open scoped Bicategory
noncomputable section
universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X U : GroupoidsOver S} (f : U ⟶ X)

/-- The source map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidSource {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    FR ⟶ FU :=
  toGroupoids.recover eR eU (KernelPair.pr1.{u + 1, u, u + 1} f)

/-- The target map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidTarget {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    FR ⟶ FU :=
  toGroupoids.recover eR eU (KernelPair.pr0.{u + 1, u, u + 1} f)

/-- The identity-arrow map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidIdentity {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    FU ⟶ FR :=
  toGroupoids.recover eU eR (FiberedCategoryOver.Groupoids.Hom.diagonal f)

/-- The inverse-arrow map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidInverse {FR : AlgebraicSpace S}
    (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    FR ⟶ FR :=
  toGroupoids.recover eR eR (TwoFibreProduct.swap.{u + 1, u, u + 1, u} f f)

/-- The first projection of the algebraic-space pullback, transported to groupoid fibrations,
induces the composite of `pullback.fst` with the source map. -/
private theorem pullbackCone_fst_induces {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    toGroupoids.InducesHom
      (toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
          (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        KernelPair.pr1.{u + 1, u, u + 1} f)
      (Bicategory.Equivalence.id _) eU
      (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
        groupoidSource f eU eR) :=
  sorry

/-- The second projection of the algebraic-space pullback, transported to groupoid fibrations,
induces the same algebraic-space map as `pullbackCone_fst_induces`. -/
private theorem pullbackCone_snd_induces {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    toGroupoids.InducesHom
      (toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
          (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        KernelPair.pr0.{u + 1, u, u + 1} f)
      (Bicategory.Equivalence.id _) eU
      (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
        groupoidSource f eU eR) :=
  sorry

/-- Whiskering the two algebraic-space pullback projections by source and target yields equal
morphisms of presented groupoid fibrations. -/
private theorem pullbackMap_eq {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    toGroupoids.map (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidSource f eU eR) =
      toGroupoids.map (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidTarget f eU eR) :=
  sorry

/-- Whiskering the two algebraic-space pullback projections by source and target yields
2-isomorphic morphisms of presented groupoid fibrations. -/
private def pullbackMapIso {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    toGroupoids.map (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidSource f eU eR) ≅
      toGroupoids.map (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidTarget f eU eR) :=
  eqToIso (pullbackMap_eq f eU eR)

/-- The presented first projection composed with `KernelPair.pr1.{u + 1, u, u + 1}` is 2-isomorphic to the ofHom of
`pullback.fst ≫ source`. -/
private def ofHomFst_comp_pr1_iso {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
        (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
      KernelPair.pr1.{u + 1, u, u + 1} f ≅
      toGroupoids.ofHom (Bicategory.Equivalence.id _) eU
        (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
          groupoidSource f eU eR) :=
  α_ ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map
          (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
      eR.inv (KernelPair.pr1.{u + 1, u, u + 1} f) ≪≫
    whiskerLeftIso
      ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map
          (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
      ((ρ_ (eR.inv ≫ KernelPair.pr1.{u + 1, u, u + 1} f)).symm ≪≫
        whiskerLeftIso (eR.inv ≫ KernelPair.pr1.{u + 1, u, u + 1} f) eU.unit ≪≫
        α_ (eR.inv ≫ KernelPair.pr1.{u + 1, u, u + 1} f) eU.hom eU.inv) ≪≫
    α_ ((Bicategory.Equivalence.id _).hom ≫
          toGroupoids.map
            (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
        ((eR.inv ≫ KernelPair.pr1.{u + 1, u, u + 1} f) ≫ eU.hom) eU.inv ≪≫
    whiskerRightIso
      (α_ (Bicategory.Equivalence.id _).hom
          (toGroupoids.map
            (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
          ((eR.inv ≫ KernelPair.pr1.{u + 1, u, u + 1} f) ≫ eU.hom)).symm
      eU.inv ≪≫
    whiskerRightIso
      (whiskerLeftIso (Bicategory.Equivalence.id _).hom
        (whiskerLeftIso
          (toGroupoids.map
            (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
          (toGroupoids.evalMapIso ((eR.inv ≫ KernelPair.pr1.{u + 1, u, u + 1} f) ≫ eU.hom))))
      eU.inv

/-- The presented second projection composed with `KernelPair.pr0.{u + 1, u, u + 1}` is 2-isomorphic to the ofHom of
`pullback.snd ≫ target`. -/
private def ofHomSnd_comp_pr0_iso {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
        (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
      KernelPair.pr0.{u + 1, u, u + 1} f ≅
      toGroupoids.ofHom (Bicategory.Equivalence.id _) eU
        (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
          groupoidTarget f eU eR) :=
  α_ ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map
          (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
      eR.inv (KernelPair.pr0.{u + 1, u, u + 1} f) ≪≫
    whiskerLeftIso
      ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map
          (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
      ((ρ_ (eR.inv ≫ KernelPair.pr0.{u + 1, u, u + 1} f)).symm ≪≫
        whiskerLeftIso (eR.inv ≫ KernelPair.pr0.{u + 1, u, u + 1} f) eU.unit ≪≫
        α_ (eR.inv ≫ KernelPair.pr0.{u + 1, u, u + 1} f) eU.hom eU.inv) ≪≫
    α_ ((Bicategory.Equivalence.id _).hom ≫
          toGroupoids.map
            (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
        ((eR.inv ≫ KernelPair.pr0.{u + 1, u, u + 1} f) ≫ eU.hom) eU.inv ≪≫
    whiskerRightIso
      (α_ (Bicategory.Equivalence.id _).hom
          (toGroupoids.map
            (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
          ((eR.inv ≫ KernelPair.pr0.{u + 1, u, u + 1} f) ≫ eU.hom)).symm
      eU.inv ≪≫
    whiskerRightIso
      (whiskerLeftIso (Bicategory.Equivalence.id _).hom
        (whiskerLeftIso
          (toGroupoids.map
            (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
          (toGroupoids.evalMapIso ((eR.inv ≫ KernelPair.pr0.{u + 1, u, u + 1} f) ≫ eU.hom))))
      eU.inv

/-- The unique comparison 2-iso between the two pullback projections. -/
private def pullbackProjectionsIso {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
        (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
      KernelPair.pr1.{u + 1, u, u + 1} f ≅
      toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
        (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
      KernelPair.pr0.{u + 1, u, u + 1} f :=
  ofHomFst_comp_pr1_iso f eU eR ≪≫
    whiskerRightIso
      (whiskerLeftIso (Bicategory.Equivalence.id _).hom
        (pullbackMapIso f eU eR))
      eU.inv ≪≫
    (ofHomSnd_comp_pr0_iso f eU eR).symm

/-- The cone on `(pr₁, pr₀)` with apex the groupoid fibration of the algebraic-space
pullback of source and target. -/
private def pullbackCone {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    PseudoPullbackCone (KernelPair.pr1.{u + 1, u, u + 1} f) (KernelPair.pr0.{u + 1, u, u + 1} f) where
  pt := (pullback (groupoidSource f eU eR) (groupoidTarget f eU eR)).toGroupoids
  fst :=
    toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
      (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR))
  snd :=
    toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
      (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR))
  iso := pullbackProjectionsIso f eU eR

/-- The 1-morphism from the algebraic-space pullback of source and target to the kernel
pair, obtained by lifting the two pullback projections. -/
def pullbackToPair {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    (pullback (groupoidSource f eU eR) (groupoidTarget f eU eR)).toGroupoids ⟶
      KernelPair.composablePairs.{u + 1, u, u + 1} f :=
  TwoFibreProduct.lift (pullbackCone f eU eR)

/-- The composition map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidCompose {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    pullback (groupoidSource f eU eR) (groupoidTarget f eU eR) ⟶ FR :=
  toGroupoids.recover (Bicategory.Equivalence.id _) eR
    (pullbackToPair f eU eR ≫ KernelPair.pr02.{u + 1, u, u + 1} f)

/-- The kernel-pair groupoid in algebraic spaces associated to `f`, relative to chosen
presentations of `U` and of the kernel pair. -/
def groupoidWith {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) where
  U := (extendBaseOver (𝟙 S)).obj FU
  R := (extendBaseOver (𝟙 S)).obj FR
  s := (extendBaseOver (𝟙 S)).map (groupoidSource f eU eR)
  t := (extendBaseOver (𝟙 S)).map (groupoidTarget f eU eR)
  c :=
    (PreservesPullback.iso (extendBaseOver (𝟙 S)) (groupoidSource f eU eR)
          (groupoidTarget f eU eR)).inv ≫
      (extendBaseOver (𝟙 S)).map (groupoidCompose f eU eR)
  e := (extendBaseOver (𝟙 S)).map (groupoidIdentity f eU eR)
  i := (extendBaseOver (𝟙 S)).map (groupoidInverse f eR)
  comp_source := sorry
  comp_target := sorry
  identity_source := sorry
  identity_target := sorry
  inverse_source := sorry
  inverse_target := sorry
  associativity := sorry
  right_identity := sorry
  left_identity := sorry
  inverse_comp := sorry
  comp_inverse := sorry

/-- The object space of `groupoidWith` is the extension of the chosen presentation of `U`. -/
theorem groupoidWith_U {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    (groupoidWith f eU eR).U = (extendBaseOver (𝟙 S)).obj FU := rfl

/-- The arrow space of `groupoidWith` is the extension of the chosen presentation of `R`. -/
theorem groupoidWith_R {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    (groupoidWith f eU eR).R = (extendBaseOver (𝟙 S)).obj FR := rfl

/-- The kernel-pair groupoid in algebraic spaces over `S` associated to a 1-morphism from a
space-representable algebraic stack. -/
def groupoid [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) :=
  groupoidWith f (IsRepresentableByAlgebraicSpace.representingEquiv hU)
    (IsRepresentableByAlgebraicSpace.representingEquiv (kernelPair_isRepresentableByAlgebraicSpace f hU))

/-- The object space of the kernel-pair groupoid presents `U`. -/
theorem groupoid_U_spec [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    Nonempty (U ≌ ((groupoid f hU).U.left).toGroupoids) :=
  sorry

/-- The arrow space of the kernel-pair groupoid presents the kernel pair. -/
theorem groupoid_R_spec [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    Nonempty (KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ ((groupoid f hU).R.left).toGroupoids) :=
  sorry

/-- The source map of the kernel-pair groupoid induces `KernelPair.pr1.{u + 1, u, u + 1}`. -/
theorem groupoid_s_induces [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    toGroupoids.InducesHom (KernelPair.pr1.{u + 1, u, u + 1} f) (IsRepresentableByAlgebraicSpace.representingEquiv
        (kernelPair_isRepresentableByAlgebraicSpace f hU))
      (IsRepresentableByAlgebraicSpace.representingEquiv hU) (groupoidSource f (IsRepresentableByAlgebraicSpace.representingEquiv hU)
        (IsRepresentableByAlgebraicSpace.representingEquiv (kernelPair_isRepresentableByAlgebraicSpace f hU))) :=
  sorry

/-- The target map of the kernel-pair groupoid induces `KernelPair.pr0.{u + 1, u, u + 1}`. -/
theorem groupoid_t_induces [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    toGroupoids.InducesHom (KernelPair.pr0.{u + 1, u, u + 1} f) (IsRepresentableByAlgebraicSpace.representingEquiv
        (kernelPair_isRepresentableByAlgebraicSpace f hU))
      (IsRepresentableByAlgebraicSpace.representingEquiv hU) (groupoidTarget f (IsRepresentableByAlgebraicSpace.representingEquiv hU)
        (IsRepresentableByAlgebraicSpace.representingEquiv (kernelPair_isRepresentableByAlgebraicSpace f hU))) :=
  sorry

/-- The composition map of the kernel-pair groupoid is recovered from `KernelPair.pr02.{u + 1, u, u + 1}`
after transporting the algebraic-space pullback to the kernel-pair fibre product. -/
theorem groupoid_c_induces {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : KernelPair.kernelPair.{u + 1, u, u + 1} f ≌ FR.toGroupoids) :
    toGroupoids.InducesHom (pullbackToPair f eU eR ≫ KernelPair.pr02.{u + 1, u, u + 1} f)
      (Bicategory.Equivalence.id _) eR (groupoidCompose f eU eR) :=
  sorry

