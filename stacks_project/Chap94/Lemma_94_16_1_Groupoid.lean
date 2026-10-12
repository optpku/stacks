/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import stacks_project.Chap65.Lemma_65_16_3
public import stacks_project.Chap94.«94_8_2_1_FullyFaithful»
public import stacks_project.Chap94.Lemma_94_16_1_KernelPair
public import stacks_project.Chap78.Definition_78_11_1_Groupoid

/-!
# Kernel-pair groupoid in algebraic spaces

Transfer of the self 2-fibre product of a 1-morphism `f : U ⟶ X` to a groupoid in
algebraic spaces over `S`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits Bicategory
open FiberedCategoryOver.Groupoids BasedNatIso
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} {X U : GroupoidsOver S}

/-- A chosen algebraic space representing a space-representable groupoid fibration. -/
def representingSpace {Y : GroupoidsOver S} (hY : IsRepresentableByAlgebraicSpace Y) :
    AlgebraicSpace S :=
  Classical.choose hY

/-- A chosen equivalence from a space-representable groupoid fibration to the groupoid
fibration of `representingSpace`. -/
def representingEquiv {Y : GroupoidsOver S} (hY : IsRepresentableByAlgebraicSpace Y) :
    Y ≌ (representingSpace hY).toGroupoids :=
  Classical.choice (Classical.choose_spec hY)

/-- `representingSpace hY` is a witness to space-representability of `Y`. -/
theorem representingSpace_spec {Y : GroupoidsOver S}
    (hY : IsRepresentableByAlgebraicSpace Y) :
    Nonempty (Y ≌ (representingSpace hY).toGroupoids) :=
  sorry

/-- Slice objects of algebraic spaces over `S`, viewed in `Over (ofOver (Over.mk (𝟙 S)))`. -/
abbrev overS : AlgebraicSpace S ⥤ Over (ofOver (Over.mk (𝟙 S))) :=
  extendBaseOver (𝟙 S)

/-- `overS` is `extendBaseOver` along `𝟙 S`. -/
theorem overS_eq : overS = extendBaseOver (𝟙 S) :=
  sorry

variable (f : U ⟶ X)

/-- The source map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidSource {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    FR ⟶ FU :=
  toGroupoids.recover eR eU (pr1 f)

/-- The target map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidTarget {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    FR ⟶ FU :=
  toGroupoids.recover eR eU (pr0 f)

/-- The identity-arrow map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidIdentity {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    FU ⟶ FR :=
  toGroupoids.recover eU eR (identityHom f)

/-- The inverse-arrow map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidInverse {FR : AlgebraicSpace S}
    (eR : kernelPair f ≌ FR.toGroupoids) :
    FR ⟶ FR :=
  toGroupoids.recover eR eR (TwoFibreProduct.swap.{u + 1, u, u + 1, u} f f)

/-- `groupoidInverse` is recovered from the symmetry of the self 2-fibre product. -/
theorem groupoidInverse_eq {FR : AlgebraicSpace S}
    (eR : kernelPair f ≌ FR.toGroupoids) :
    groupoidInverse f eR =
      toGroupoids.recover eR eR (TwoFibreProduct.swap.{u + 1, u, u + 1, u} f f) :=
  sorry

/-- The two projections of the algebraic-space pullback compose equally to `U`. -/
theorem pullback_source_eq_target {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
        groupoidSource f eU eR =
      pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
        groupoidTarget f eU eR :=
  sorry

/-- The first projection of the algebraic-space pullback, transported to groupoid fibrations,
induces the composite of `pullback.fst` with the source map. -/
theorem pullbackCone_fst_induces {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    toGroupoids.InducesHom
      (toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
          (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        pr1 f)
      (Bicategory.Equivalence.id _) eU
      (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
        groupoidSource f eU eR) :=
  sorry

/-- The second projection of the algebraic-space pullback, transported to groupoid fibrations,
induces the same algebraic-space map as `pullbackCone_fst_induces`. -/
theorem pullbackCone_snd_induces {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    toGroupoids.InducesHom
      (toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
          (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        pr0 f)
      (Bicategory.Equivalence.id _) eU
      (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
        groupoidSource f eU eR) :=
  sorry

/-- On objects, a presented `1`-morphism agrees with the canonical `1`-morphism associated to
its recovered algebraic-space map. -/
theorem evalMap_obj_eq {F G : AlgebraicSpace S}
    (ψ : F.toGroupoids ⟶ G.toGroupoids) :
    ∀ x, ψ.hom.obj x = (toGroupoids.map (toGroupoids.eval ψ)).hom.obj x :=
  sorry

/-- The morphism of presented groupoid fibrations associated to `ψ` is 2-isomorphic to
`toGroupoids.map (eval ψ)`. -/
def evalMapIso {F G : AlgebraicSpace S} (ψ : F.toGroupoids ⟶ G.toGroupoids) :
    ψ ≅ toGroupoids.map (toGroupoids.eval ψ) :=
  Bicategory.InducedBicategory.isoMk
    (BasedNatIso.ofComponents (fun x => eqToIso (evalMap_obj_eq ψ x))
      (fun {_ _} _ => sorry) (fun _ => sorry))

/-- `evalMapIso` exhibits the source `1`-morphism as `2`-isomorphic to the canonical image of
its recovered algebraic-space map. -/
theorem evalMapIso_spec {F G : AlgebraicSpace S}
    (ψ : F.toGroupoids ⟶ G.toGroupoids) :
    IsIsomorphic ψ (toGroupoids.map (toGroupoids.eval ψ)) :=
  sorry

/-- Whiskering the two algebraic-space pullback projections by source and target yields equal
morphisms of presented groupoid fibrations. -/
theorem pullbackMap_eq {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    toGroupoids.map (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidSource f eU eR) =
      toGroupoids.map (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidTarget f eU eR) :=
  sorry

/-- Whiskering the two algebraic-space pullback projections by source and target yields
2-isomorphic morphisms of presented groupoid fibrations. -/
def pullbackMapIso {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    toGroupoids.map (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidSource f eU eR) ≅
      toGroupoids.map (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidTarget f eU eR) :=
  eqToIso (pullbackMap_eq f eU eR)

/-- `pullbackMapIso` is the `2`-iso associated to equality of the whiskered pullback
projections. -/
theorem pullbackMapIso_spec {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    IsIsomorphic
      (toGroupoids.map (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidSource f eU eR))
      (toGroupoids.map (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
        toGroupoids.map (groupoidTarget f eU eR)) :=
  sorry

/-- The presented first projection composed with `pr1` is 2-isomorphic to the ofHom of
`pullback.fst ≫ source`. -/
def ofHomFst_comp_pr1_iso {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
        (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
      pr1 f ≅
      toGroupoids.ofHom (Bicategory.Equivalence.id _) eU
        (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
          groupoidSource f eU eR) :=
  α_ ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map
          (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
      eR.inv (pr1 f) ≪≫
    whiskerLeftIso
      ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map
          (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
      ((ρ_ (eR.inv ≫ pr1 f)).symm ≪≫
        whiskerLeftIso (eR.inv ≫ pr1 f) eU.unit ≪≫
        α_ (eR.inv ≫ pr1 f) eU.hom eU.inv) ≪≫
    α_ ((Bicategory.Equivalence.id _).hom ≫
          toGroupoids.map
            (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
        ((eR.inv ≫ pr1 f) ≫ eU.hom) eU.inv ≪≫
    whiskerRightIso
      (α_ (Bicategory.Equivalence.id _).hom
          (toGroupoids.map
            (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
          ((eR.inv ≫ pr1 f) ≫ eU.hom)).symm
      eU.inv ≪≫
    whiskerRightIso
      (whiskerLeftIso (Bicategory.Equivalence.id _).hom
        (whiskerLeftIso
          (toGroupoids.map
            (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)))
          (evalMapIso ((eR.inv ≫ pr1 f) ≫ eU.hom))))
      eU.inv

/-- The presented second projection composed with `pr0` is 2-isomorphic to the ofHom of
`pullback.snd ≫ target`. -/
def ofHomSnd_comp_pr0_iso {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
        (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
      pr0 f ≅
      toGroupoids.ofHom (Bicategory.Equivalence.id _) eU
        (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR) ≫
          groupoidTarget f eU eR) :=
  α_ ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map
          (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
      eR.inv (pr0 f) ≪≫
    whiskerLeftIso
      ((Bicategory.Equivalence.id _).hom ≫
        toGroupoids.map
          (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
      ((ρ_ (eR.inv ≫ pr0 f)).symm ≪≫
        whiskerLeftIso (eR.inv ≫ pr0 f) eU.unit ≪≫
        α_ (eR.inv ≫ pr0 f) eU.hom eU.inv) ≪≫
    α_ ((Bicategory.Equivalence.id _).hom ≫
          toGroupoids.map
            (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
        ((eR.inv ≫ pr0 f) ≫ eU.hom) eU.inv ≪≫
    whiskerRightIso
      (α_ (Bicategory.Equivalence.id _).hom
          (toGroupoids.map
            (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
          ((eR.inv ≫ pr0 f) ≫ eU.hom)).symm
      eU.inv ≪≫
    whiskerRightIso
      (whiskerLeftIso (Bicategory.Equivalence.id _).hom
        (whiskerLeftIso
          (toGroupoids.map
            (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)))
          (evalMapIso ((eR.inv ≫ pr0 f) ≫ eU.hom))))
      eU.inv

/-- The unique comparison 2-iso between the two pullback projections. -/
def pullbackProjectionsIso {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
        (pullback.fst (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
      pr1 f ≅
      toGroupoids.ofHom (Bicategory.Equivalence.id _) eR
        (pullback.snd (groupoidSource f eU eR) (groupoidTarget f eU eR)) ≫
      pr0 f :=
  ofHomFst_comp_pr1_iso f eU eR ≪≫
    whiskerRightIso
      (whiskerLeftIso (Bicategory.Equivalence.id _).hom
        (pullbackMapIso f eU eR))
      eU.inv ≪≫
    (ofHomSnd_comp_pr0_iso f eU eR).symm

/-- The cone on `(pr₁, pr₀)` with apex the groupoid fibration of the algebraic-space
pullback of source and target. -/
def pullbackCone {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    PseudoPullbackCone (pr1 f) (pr0 f) where
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
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    (pullback (groupoidSource f eU eR) (groupoidTarget f eU eR)).toGroupoids ⟶
      kernelPairPair f :=
  PseudoPullbackCone.lift (pullbackCone f eU eR)
    (TwoFibreProduct.cone.{u + 1, u, u + 1, u} (pr1 f) (pr0 f))

/-- The composition map of the kernel-pair groupoid, as a morphism of algebraic spaces. -/
def groupoidCompose {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    pullback (groupoidSource f eU eR) (groupoidTarget f eU eR) ⟶ FR :=
  toGroupoids.recover (Bicategory.Equivalence.id _) eR
    (pullbackToPair f eU eR ≫ pr02 f)

/-- The kernel-pair groupoid in algebraic spaces associated to `f`, relative to chosen
presentations of `U` and of the kernel pair. -/
def groupoidWith {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) where
  U := overS.obj FU
  R := overS.obj FR
  s := overS.map (groupoidSource f eU eR)
  t := overS.map (groupoidTarget f eU eR)
  c :=
    (PreservesPullback.iso overS (groupoidSource f eU eR)
          (groupoidTarget f eU eR)).inv ≫
      overS.map (groupoidCompose f eU eR)
  e := overS.map (groupoidIdentity f eU eR)
  i := overS.map (groupoidInverse f eR)
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
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    (groupoidWith f eU eR).U = overS.obj FU :=
  sorry

/-- The arrow space of `groupoidWith` is the extension of the chosen presentation of `R`. -/
theorem groupoidWith_R {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    (groupoidWith f eU eR).R = overS.obj FR :=
  sorry

/-- The kernel-pair groupoid in algebraic spaces over `S` associated to a 1-morphism from a
space-representable algebraic stack. -/
def groupoid [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    GroupoidAlgebraicSpace (ofOver (Over.mk (𝟙 S))) :=
  groupoidWith f (representingEquiv hU)
    (representingEquiv (kernelPair_isRepresentableByAlgebraicSpace f hU))

/-- The object space of the kernel-pair groupoid presents `U`. -/
theorem groupoid_U_spec [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    Nonempty (U ≌ ((groupoid f hU).U.left).toGroupoids) :=
  sorry

/-- The arrow space of the kernel-pair groupoid presents the kernel pair. -/
theorem groupoid_R_spec [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    Nonempty (kernelPair f ≌ ((groupoid f hU).R.left).toGroupoids) :=
  sorry

/-- The source map of the kernel-pair groupoid induces `pr1`. -/
theorem groupoid_s_induces [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    toGroupoids.InducesHom (pr1 f) (representingEquiv
        (kernelPair_isRepresentableByAlgebraicSpace f hU))
      (representingEquiv hU) (groupoidSource f (representingEquiv hU)
        (representingEquiv (kernelPair_isRepresentableByAlgebraicSpace f hU))) :=
  sorry

/-- The target map of the kernel-pair groupoid induces `pr0`. -/
theorem groupoid_t_induces [AlgebraicStack X] (hU : IsRepresentableByAlgebraicSpace U) :
    toGroupoids.InducesHom (pr0 f) (representingEquiv
        (kernelPair_isRepresentableByAlgebraicSpace f hU))
      (representingEquiv hU) (groupoidTarget f (representingEquiv hU)
        (representingEquiv (kernelPair_isRepresentableByAlgebraicSpace f hU))) :=
  sorry

/-- The composition map of the kernel-pair groupoid is recovered from `pr02`
after transporting the algebraic-space pullback to the kernel-pair fibre product. -/
theorem groupoid_c_induces {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    toGroupoids.InducesHom (pullbackToPair f eU eR ≫ pr02 f)
      (Bicategory.Equivalence.id _) eR (groupoidCompose f eU eR) :=
  sorry

/-- `groupoidSource` is the algebraic-space map recovered from `pr1`. -/
theorem groupoidSource_eq {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    groupoidSource f eU eR = toGroupoids.recover eR eU (pr1 f) :=
  sorry

/-- `groupoidTarget` is the algebraic-space map recovered from `pr0`. -/
theorem groupoidTarget_eq {FU FR : AlgebraicSpace S}
    (eU : U ≌ FU.toGroupoids) (eR : kernelPair f ≌ FR.toGroupoids) :
    groupoidTarget f eU eR = toGroupoids.recover eR eU (pr0 f) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
