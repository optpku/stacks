module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import stacks_project.Chap65.Lemma_65_9_1_KernelPair
public import stacks_project.Chap66.Lemma_66_6_7
public import stacks_project.Chap66.Lemma_66_18_3_Etale
public import stacks_project.Chap66.«66_26_1_1_Restrict»

/-!
# Kernel-pair exact sequence of module pushforwards

For an étale morphism `π : U ⟶ X` from a scheme, the kernel pair `R = U ×_X U`
supplies projections `t, s : R ⟶ U`. Restriction and pushforward along these
étale maps assemble the two canonical arrows `f_* F ⟶ a_*(F|_U) ⟶ b_*(F|_R)`
used to compute module pushforward along a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits
open CategoryTheory.Sheaf.InternalModule

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} {U : Over S}

/-- An étale morphism from a scheme to an algebraic space, in the sense of the
relative étale presheaf property, is étale as a morphism of algebraic spaces. -/
theorem etale_of_presheaf (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    Etale π :=
  (isEtale_iff_isEtaleFromScheme π).mpr hπ

/-- The projection `t : R ⟶ U` of the kernel pair `R = U ×_X U`. -/
def t (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    ofOver (kernelPair π hπ.rep).left ⟶ ofOver U :=
  ofOverMap (hπ.rep.fst' π)

/-- The projection `s : R ⟶ U` of the kernel pair `R = U ×_X U`. -/
def s (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    ofOver (kernelPair π hπ.rep).left ⟶ ofOver U :=
  ofOverMap (hπ.rep.snd π)

/-- `t` is `ofOverMap` of the first relatively representable kernel-pair projection. -/
theorem t_eq (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    t π hπ = ofOverMap (hπ.rep.fst' π) :=
  sorry

/-- `s` is `ofOverMap` of the second relatively representable kernel-pair projection. -/
theorem s_eq (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    s π hπ = ofOverMap (hπ.rep.snd π) :=
  sorry

/-- `t` agrees with the first projection of the represented kernel pair. -/
theorem t_eq_kernelPair (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    t π hπ = ofOverMap (kernelPair π hπ.rep).t :=
  sorry

/-- `s` agrees with the second projection of the represented kernel pair. -/
theorem s_eq_kernelPair (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    s π hπ = ofOverMap (kernelPair π hπ.rep).s :=
  sorry

/-- The two kernel-pair projections become equal after composition with `π`. -/
def t_comp_eq_s_comp (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    t π hπ ≫ π = s π hπ ≫ π :=
  (congrArg (fun φ ↦ φ ≫ π) (hπ.rep.map_fst' π)).trans (hπ.rep.w π)

/-- `t ≫ π` is the kernel-pair morphism `kernelPairHom π hπ`. -/
theorem t_comp_eq_kernelPairHom (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    t π hπ ≫ π = kernelPairHom π hπ :=
  sorry

/-- `s ≫ π` is the kernel-pair morphism `kernelPairHom π hπ`. -/
theorem s_comp_eq_kernelPairHom (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    s π hπ ≫ π = kernelPairHom π hπ :=
  sorry

/-- The first kernel-pair projection is étale as a morphism of algebraic spaces. -/
instance etale_t (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    Etale (t π hπ) :=
  sorry

/-- The second kernel-pair projection is étale as a morphism of algebraic spaces. -/
instance etale_s (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    Etale (s π hπ) :=
  sorry

/-- The composite of the first kernel-pair projection with `π` is étale. -/
instance etale_t_comp_π (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    Etale (t π hπ ≫ π) :=
  Etale.etale_comp (t π hπ) π

/-- The composite of the second kernel-pair projection with `π` is étale. -/
instance etale_s_comp_π (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    Etale (s π hπ ≫ π) :=
  Etale.etale_comp (s π hπ) π

/-- Identity-on-left comparison of successive étale postcomposition functors with
postcomposition along the composite. -/
def restrictPostcomposeCompIso (f : X ⟶ Y) [Etale f] (g : Y ⟶ Z) [Etale g] :
    restrictPostcompose f ⋙ restrictPostcompose g ≅ restrictPostcompose (f ≫ g) :=
  NatIso.ofComponents
    (fun _ ↦
      { hom := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry
        inv := MorphismProperty.CostructuredArrow.homMk (𝟙 _) trivial sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- The forward component of `restrictPostcomposeCompIso` is the identity on underlying
schemes over `S`. -/
theorem restrictPostcomposeCompIso_hom_app_left (f : X ⟶ Y) [Etale f] (g : Y ⟶ Z) [Etale g]
    (W : smallEtaleSite X) :
    ((restrictPostcomposeCompIso f g).hom.app W).left = 𝟙 _ :=
  sorry

/-- Continuous composite of successive étale postcomposition functors. -/
instance restrictPostcompose_comp_isContinuous (f : X ⟶ Y) [Etale f] (g : Y ⟶ Z) [Etale g] :
    (restrictPostcompose f ⋙ restrictPostcompose g).IsContinuous
      (smallEtaleTopology X) (smallEtaleTopology Z) :=
  Functor.isContinuous_comp (restrictPostcompose f) (restrictPostcompose g)
    (smallEtaleTopology X) (smallEtaleTopology Y) (smallEtaleTopology Z)

/-- Restriction of modules along an étale composite is the composite of the restrictions. -/
def restrictFunctorCompIso (f : X ⟶ Y) [Etale f] (g : Y ⟶ Z) [Etale g] :
    restrictFunctor g ⋙ restrictFunctor f ≅ restrictFunctor (f ≫ g) :=
  NatIso.ofComponents
    (fun M ↦
      { hom :=
          homOfUnderlying (structureSheaf X)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        inv :=
          homOfUnderlying (structureSheaf X)
            (InducedCategory.homMk
              { app := fun _ ↦ 𝟙 _
                naturality := fun _ _ _ ↦ sorry })
            sorry sorry
        hom_inv_id := sorry
        inv_hom_id := sorry })
    sorry

/-- Pushforward of modules along an étale composite is the composite of the pushforwards. -/
def pushforwardCompIso_etale (f : X ⟶ Y) [Etale f] (g : Y ⟶ Z) [Etale g] :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  Adjunction.rightAdjointUniq
    (((restrictAdjunction g).comp (restrictAdjunction f)).ofNatIsoLeft
      (restrictFunctorCompIso f g))
    (restrictAdjunction (f ≫ g))

/-- The composite pushforward `a_* = f_* ∘ π_*` implementing direct image along `a = π ≫ f`. -/
def inducedPushforward (f : X ⟶ Y) (π : ofOver U ⟶ X) :
    (ofOver U).Modules ⥤ Y.Modules :=
  pushforward π ⋙ pushforward f

/-- `inducedPushforward f π` is the composite of étale pushforward along `π` with
pushforward along `f`. -/
theorem inducedPushforward_eq (f : X ⟶ Y) (π : ofOver U ⟶ X) :
    inducedPushforward f π = pushforward π ⋙ pushforward f :=
  sorry

/-- The composite pushforward `b_* = f_* ∘ (t ≫ π)_*` implementing direct image along
`b = t ≫ π ≫ f`. -/
def kernelPairPushforward (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    (ofOver (kernelPair π hπ.rep).left).Modules ⥤ Y.Modules :=
  pushforward (t π hπ ≫ π) ⋙ pushforward f

/-- `kernelPairPushforward` is pushforward along `t ≫ π` followed by pushforward along `f`. -/
theorem kernelPairPushforward_eq (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    kernelPairPushforward f π hπ = pushforward (t π hπ ≫ π) ⋙ pushforward f :=
  sorry

/-- Restriction of an `𝒪_X`-module to the kernel pair `R = U ×_X U`. -/
def restrictToKernelPair (F : X.Modules) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    (ofOver (kernelPair π hπ.rep).left).Modules :=
  restrict F (t π hπ ≫ π)

/-- `restrictToKernelPair F π hπ` is restriction of `F` along `t ≫ π`. -/
theorem restrictToKernelPair_eq (F : X.Modules) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    restrictToKernelPair F π hπ = restrict F (t π hπ ≫ π) :=
  sorry

/-- An étale morphism of algebraic spaces, bundled with its étale witness. -/
def EtaleHom (X Y : AlgebraicSpace S) :=
  { f : X ⟶ Y // Etale f }

/-- Restriction of a module along a bundled étale morphism. -/
def restrictOn {R : AlgebraicSpace S} (F : X.Modules) (φ : EtaleHom R X) : R.Modules :=
  @restrict S R X F φ.val φ.property

/-- The bundled étale morphism `t ≫ π`. -/
def etaleHom_t_comp (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    EtaleHom (ofOver (kernelPair π hπ.rep).left) X :=
  ⟨t π hπ ≫ π, etale_t_comp_π π hπ⟩

/-- The bundled étale morphism `s ≫ π`. -/
def etaleHom_s_comp (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    EtaleHom (ofOver (kernelPair π hπ.rep).left) X :=
  ⟨s π hπ ≫ π, etale_s_comp_π π hπ⟩

/-- The bundled morphisms `s ≫ π` and `t ≫ π` agree. -/
def etaleHom_s_comp_eq_t_comp (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    etaleHom_s_comp π hπ = etaleHom_t_comp π hπ :=
  Subtype.ext (t_comp_eq_s_comp π hπ).symm

/-- Restriction of `F` along `s ≫ π` agrees with restriction along `t ≫ π`. -/
def restrictOn_s_comp_eq_t_comp (F : X.Modules) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    restrictOn F (etaleHom_s_comp π hπ) = restrictOn F (etaleHom_t_comp π hπ) :=
  congrArg (restrictOn F) (etaleHom_s_comp_eq_t_comp π hπ)

/-- The first arrow `f_* F ⟶ a_*(F|_U)` is `f_*` of the restriction–pushforward unit of `π`. -/
def pushforwardIncl (f : X ⟶ Y) (π : ofOver U ⟶ X) [Etale π] (F : X.Modules) :
    (pushforward f).obj F ⟶ (inducedPushforward f π).obj (restrict F π) :=
  (pushforward f).map ((restrictAdjunction π).unit.app F)

/-- `pushforwardIncl` is `f_*` of the unit of `restrictAdjunction π`. -/
theorem pushforwardIncl_eq (f : X ⟶ Y) (π : ofOver U ⟶ X) [Etale π] (F : X.Modules) :
    pushforwardIncl f π F =
      (pushforward f).map ((restrictAdjunction π).unit.app F) :=
  sorry

/-- Reassociation of `π_* ∘ t_*` into `(t ≫ π)_*` after identifying `(F|_U)|_R` with `F|_R`. -/
def restrictionReassocT (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (inducedPushforward f π).obj
        ((pushforward (t π hπ)).obj ((restrictFunctor (t π hπ)).obj (restrict F π))) ⟶
      (kernelPairPushforward f π hπ).obj (restrictToKernelPair F π hπ) :=
  (pushforward f).map
    ((pushforwardCompIso_etale (t π hπ) π).hom.app
        ((restrictFunctor (t π hπ)).obj (restrict F π)) ≫
      (pushforward (t π hπ ≫ π)).map ((restrictFunctorCompIso (t π hπ) π).hom.app F))

/-- Reassociation of `π_* ∘ s_*` into `(t ≫ π)_*` after identifying `(F|_U)|_R` with `F|_R`. -/
def restrictionReassocS (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (inducedPushforward f π).obj
        ((pushforward (s π hπ)).obj ((restrictFunctor (s π hπ)).obj (restrict F π))) ⟶
      (kernelPairPushforward f π hπ).obj (restrictToKernelPair F π hπ) :=
  (pushforward f).map
    ((pushforwardCompIso_etale (s π hπ) π).hom.app
        ((restrictFunctor (s π hπ)).obj (restrict F π)) ≫
      (eqToHom (congrArg (fun φ ↦ (pushforward φ).obj
          ((restrictFunctor (s π hπ)).obj (restrict F π)))
        (t_comp_eq_s_comp π hπ).symm) ≫
        (pushforward (t π hπ ≫ π)).map
          ((restrictFunctorCompIso (s π hπ) π).hom.app F ≫
            eqToHom (restrictOn_s_comp_eq_t_comp F π hπ))))

/-- The map `t* : a_*(F|_U) ⟶ b_*(F|_R)` induced by restriction along `t`. -/
def restrictionAlongT (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (inducedPushforward f π).obj (restrict F π) ⟶
      (kernelPairPushforward f π hπ).obj (restrictToKernelPair F π hπ) :=
  (inducedPushforward f π).map ((restrictAdjunction (t π hπ)).unit.app (restrict F π)) ≫
    restrictionReassocT f π hπ F

/-- `restrictionAlongT` is the unit of restriction along `t`, reassociated into `b_*`. -/
theorem restrictionAlongT_eq (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    restrictionAlongT f π hπ F =
      (inducedPushforward f π).map ((restrictAdjunction (t π hπ)).unit.app (restrict F π)) ≫
        restrictionReassocT f π hπ F :=
  sorry

/-- The map `s* : a_*(F|_U) ⟶ b_*(F|_R)` induced by restriction along `s`. -/
def restrictionAlongS (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (inducedPushforward f π).obj (restrict F π) ⟶
      (kernelPairPushforward f π hπ).obj (restrictToKernelPair F π hπ) :=
  (inducedPushforward f π).map ((restrictAdjunction (s π hπ)).unit.app (restrict F π)) ≫
    restrictionReassocS f π hπ F

/-- `restrictionAlongS` is the unit of restriction along `s`, reassociated into `b_*`. -/
theorem restrictionAlongS_eq (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    restrictionAlongS f π hπ F =
      (inducedPushforward f π).map ((restrictAdjunction (s π hπ)).unit.app (restrict F π)) ≫
        restrictionReassocS f π hπ F :=
  sorry

/-- The second arrow `a_*(F|_U) ⟶ b_*(F|_R)` is the difference `t* - s*`. -/
def restrictionDiff (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (inducedPushforward f π).obj (restrict F π) ⟶
      (kernelPairPushforward f π hπ).obj (restrictToKernelPair F π hπ) :=
  restrictionAlongT f π hπ F - restrictionAlongS f π hπ F

/-- `restrictionDiff` is the difference of the two restriction maps. -/
theorem restrictionDiff_eq (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    restrictionDiff f π hπ F =
      restrictionAlongT f π hπ F - restrictionAlongS f π hπ F :=
  sorry

/-- The short complex `f_* F ⟶ a_*(F|_U) ⟶ b_*(F|_R)` whose second arrow is `t* - s*`. -/
def pushforwardShortComplex (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    ShortComplex Y.Modules :=
  ShortComplex.mk (pushforwardIncl f π F) (restrictionDiff f π hπ F) sorry

/-- The first morphism of `pushforwardShortComplex` is `pushforwardIncl`. -/
theorem pushforwardShortComplex_f (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).f = pushforwardIncl f π F :=
  sorry

/-- The second morphism of `pushforwardShortComplex` is `restrictionDiff`. -/
theorem pushforwardShortComplex_g (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).g = restrictionDiff f π hπ F :=
  sorry

/-- The first object of `pushforwardShortComplex` is `f_* F`. -/
theorem pushforwardShortComplex_X₁ (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).X₁ = (pushforward f).obj F :=
  sorry

/-- The middle object of `pushforwardShortComplex` is `a_*(F|_U)`. -/
theorem pushforwardShortComplex_X₂ (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).X₂ = (inducedPushforward f π).obj (restrict F π) :=
  sorry

/-- The last object of `pushforwardShortComplex` is `b_*(F|_R)`. -/
theorem pushforwardShortComplex_X₃ (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).X₃ =
      (kernelPairPushforward f π hπ).obj (restrictToKernelPair F π hπ) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules

