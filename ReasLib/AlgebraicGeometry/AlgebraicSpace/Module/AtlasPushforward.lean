module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.KernelPair
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.RestrictionComposition

/-!
# The atlas sequence of module pushforwards

A scheme atlas and its kernel pair give the canonical inclusion and difference
of restrictions computing pushforward of arbitrary structure-sheaf modules.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules.Atlas

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} {U : Over S}

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
  rfl

/-- `s` is `ofOverMap` of the second relatively representable kernel-pair projection. -/
theorem s_eq (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    s π hπ = ofOverMap (hπ.rep.snd π) :=
  rfl

/-- `t` agrees with the first projection of the represented kernel pair. -/
theorem t_eq_kernelPair (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    t π hπ = ofOverMap (kernelPair π hπ.rep).t :=
  (congrArg ofOverMap (kernelPair_t π hπ.rep)).symm

/-- `s` agrees with the second projection of the represented kernel pair. -/
theorem s_eq_kernelPair (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    s π hπ = ofOverMap (kernelPair π hπ.rep).s :=
  (congrArg ofOverMap (kernelPair_s π hπ.rep)).symm

/-- The two kernel-pair projections become equal after composition with `π`. -/
theorem t_comp_eq_s_comp (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) :
    t π hπ ≫ π = s π hπ ≫ π :=
  (congrArg (fun φ ↦ φ ≫ π) (hπ.rep.map_fst' π)).trans (hπ.rep.w π)

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

/-- The composite pushforward `a_* = f_* ∘ π_*` implementing direct image along `a = π ≫ f`. -/
def inducedPushforward (f : X ⟶ Y) (π : ofOver U ⟶ X) :
    (ofOver U).Modules ⥤ Y.Modules :=
  pushforward π ⋙ pushforward f

/-- `inducedPushforward f π` is the composite of étale pushforward along `π` with
pushforward along `f`. -/
theorem inducedPushforward_eq (f : X ⟶ Y) (π : ofOver U ⟶ X) :
    inducedPushforward f π = pushforward π ⋙ pushforward f :=
  rfl

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
  rfl

/-- Restriction of an `𝒪_X`-module to the kernel pair `R = U ×_X U`. -/
def restrictToKernelPair (F : X.Modules) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    (ofOver (kernelPair π hπ.rep).left).Modules :=
  restrict F (t π hπ ≫ π)

/-- `restrictToKernelPair F π hπ` is restriction of `F` along `t ≫ π`. -/
theorem restrictToKernelPair_eq (F : X.Modules) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] :
    restrictToKernelPair F π hπ = restrict F (t π hπ ≫ π) :=
  rfl

/-- The first arrow `f_* F ⟶ a_*(F|_U)` is `f_*` of the restriction–pushforward unit of `π`. -/
def pushforwardIncl (f : X ⟶ Y) (π : ofOver U ⟶ X) [Etale π] (F : X.Modules) :
    (pushforward f).obj F ⟶ (inducedPushforward f π).obj (restrict F π) :=
  (pushforward f).map ((restrictAdjunction π).unit.app F)

/-- `pushforwardIncl` is `f_*` of the unit of `restrictAdjunction π`. -/
theorem pushforwardIncl_eq (f : X ⟶ Y) (π : ofOver U ⟶ X) [Etale π] (F : X.Modules) :
    pushforwardIncl f π F =
      (pushforward f).map ((restrictAdjunction π).unit.app F) :=
  rfl

/-- Reassociation of `π_* ∘ t_*` into `(t ≫ π)_*` after identifying `(F|_U)|_R` with `F|_R`. -/
def restrictionReassocT (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (inducedPushforward f π).obj
        ((pushforward (t π hπ)).obj ((restrictFunctor (t π hπ)).obj (restrict F π))) ⟶
      (kernelPairPushforward f π hπ).obj (restrictToKernelPair F π hπ) :=
  (pushforward f).map
    ((pushforwardComp (t π hπ) π).hom.app
        ((restrictFunctor (t π hπ)).obj (restrict F π)) ≫
      (pushforward (t π hπ ≫ π)).map ((restrictFunctorCompIso (t π hπ) π).hom.app F))

/-- Reassociation of `π_* ∘ s_*` into `(t ≫ π)_*` after identifying `(F|_U)|_R` with `F|_R`. -/
def restrictionReassocS (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (inducedPushforward f π).obj
        ((pushforward (s π hπ)).obj ((restrictFunctor (s π hπ)).obj (restrict F π))) ⟶
      (kernelPairPushforward f π hπ).obj (restrictToKernelPair F π hπ) :=
  (pushforward f).map
    ((pushforwardComp (s π hπ) π).hom.app
        ((restrictFunctor (s π hπ)).obj (restrict F π)) ≫
      (eqToHom (congrArg (fun φ ↦ (pushforward φ).obj
          ((restrictFunctor (s π hπ)).obj (restrict F π)))
        (t_comp_eq_s_comp π hπ).symm) ≫
        (pushforward (t π hπ ≫ π)).map
          ((restrictFunctorCompIso (s π hπ) π).hom.app F ≫
            eqToHom (restrict_eq_of_hom_eq F (s π hπ ≫ π) (t π hπ ≫ π)
              (t_comp_eq_s_comp π hπ).symm))))

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
  rfl

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
  rfl

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
  rfl

/-- The atlas inclusion followed by the difference of kernel-pair restrictions is zero. -/
theorem pushforwardIncl_comp_restrictionDiff (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π]
    (F : X.Modules) :
    pushforwardIncl f π F ≫ restrictionDiff f π hπ F = 0 :=
  sorry

/-- The short complex `f_* F ⟶ a_*(F|_U) ⟶ b_*(F|_R)` whose second arrow is `t* - s*`. -/
def pushforwardShortComplex (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    ShortComplex Y.Modules :=
  ShortComplex.mk (pushforwardIncl f π F) (restrictionDiff f π hπ F)
    (pushforwardIncl_comp_restrictionDiff f π hπ F)

/-- The first morphism of `pushforwardShortComplex` is `pushforwardIncl`. -/
theorem pushforwardShortComplex_f (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).f = pushforwardIncl f π F :=
  rfl

/-- The second morphism of `pushforwardShortComplex` is `restrictionDiff`. -/
theorem pushforwardShortComplex_g (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).g = restrictionDiff f π hπ F :=
  rfl

/-- The first object of `pushforwardShortComplex` is `f_* F`. -/
theorem pushforwardShortComplex_X₁ (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).X₁ = (pushforward f).obj F :=
  rfl

/-- The middle object of `pushforwardShortComplex` is `a_*(F|_U)`. -/
theorem pushforwardShortComplex_X₂ (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).X₂ = (inducedPushforward f π).obj (restrict F π) :=
  rfl

/-- The last object of `pushforwardShortComplex` is `b_*(F|_R)`. -/
theorem pushforwardShortComplex_X₃ (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π) [Etale π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).X₃ =
      (kernelPairPushforward f π hπ).obj (restrictToKernelPair F π hπ) :=
  rfl

/-- For a surjective étale scheme atlas, module pushforward is the kernel of the
difference of the two kernel-pair restrictions, and the atlas inclusion is monic. -/
theorem pushforward_exact (f : X ⟶ Y) (π : ofOver U ⟶ X)
    (hπ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf π)
    [Etale π] [Surjective π] (F : X.Modules) :
    (pushforwardShortComplex f π hπ F).Exact ∧ Mono (pushforwardIncl f π F) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.Atlas
