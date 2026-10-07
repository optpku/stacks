module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import stacks_project.Chap103.Lemma_103_10_3
public import stacks_project.Chap103.Lemma_103_10_8_Hom

/-!
# Pullback of internal Hom along a flat morphism of algebraic stacks

If `f : X ⟶ Y` is a flat morphism of algebraic stacks, `F` is a finitely
presented `𝒪_Y`-module and `G` is quasi-coherent, then
`f^* hom(F, G) ≅ hom(f^* F, f^* G)`, with `hom` as `QCoh.internalHomFP`
from Lemma 103.10.8.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open AlgebraicGeometry.GroupoidsOver
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.MonoidalCategory
open FiberedCategoryOver.Groupoids SheafOfModules.RingedSite
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
  [AlgebraicStack X] [AlgebraicStack Y]

/-- Finite presentation is preserved by pullback of fppf modules. -/
instance modulePullback_isFinitePresentation (f : X ⟶ Y) (F : fppfModules Y)
    [F.IsFinitePresentation] :
    ((modulePullback f).obj F).IsFinitePresentation :=
  sorry

/-- Finite presentation is preserved by étale inverse image. -/
instance moduleInverseImage_isFinitePresentation (f : X ⟶ Y)
    (F : etaleModules Y) [F.IsFinitePresentation] :
    ((moduleInverseImage f).obj F).IsFinitePresentation :=
  sorry

/-- Identity-on-Γ comparison of étale inverse image of a restriction with
restriction of fppf pullback. -/
def restriction_modulePullback (f : X ⟶ Y) (F : fppfModules Y) :
    (moduleInverseImage f).obj ((restriction Y).obj F) ⟶
      (restriction X).obj ((modulePullback f).obj F) where
  val :=
    { app U := moduleCatOfFun _ _ id
      naturality := sorry }

/-- Inverse of `restriction_modulePullback`. -/
def restriction_modulePullback_inv (f : X ⟶ Y) (F : fppfModules Y) :
    (restriction X).obj ((modulePullback f).obj F) ⟶
      (moduleInverseImage f).obj ((restriction Y).obj F) where
  val :=
    { app U := moduleCatOfFun _ _ id
      naturality := sorry }

/-- Evaluation of étale sheaf Hom, as the uncurrying of the identity. -/
def moduleSheafHomOnEtale_ev {Z : GroupoidsOver S} (F G : etaleModules Z)
    [F.IsFinitePresentation] :
    moduleTensorEtale (moduleSheafHomOnEtale F G) F ⟶ G :=
  moduleSheafHomOnEtale_homEquiv F G (moduleSheafHomOnEtale F G) (𝟙 _)

/-- Transport étale sheaf Hom along the restriction/pullback comparison in the
source variable (contravariant) and the target variable (covariant). -/
def moduleSheafHomOnEtale_restrictionPullback (f : X ⟶ Y)
    (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation] :
    moduleSheafHomOnEtale
        ((moduleInverseImage f).obj ((restriction Y).obj F))
        ((moduleInverseImage f).obj ((restriction Y).obj G.obj)) ⟶
      moduleSheafHomOnEtale ((restriction X).obj ((modulePullback f).obj F))
        ((restriction X).obj ((QCoh.pullback f).obj G).obj) :=
  (moduleSheafHomOnEtale_homEquiv
      ((restriction X).obj ((modulePullback f).obj F))
      ((restriction X).obj ((QCoh.pullback f).obj G).obj)
      (moduleSheafHomOnEtale
        ((moduleInverseImage f).obj ((restriction Y).obj F))
        ((moduleInverseImage f).obj ((restriction Y).obj G.obj)))).symm
    (SheafOfModules.RingedSite.moduleTensorMap.{u + 1, u, u}
        (𝟙 _) (restriction_modulePullback_inv f F) ≫
      moduleSheafHomOnEtale_ev
        ((moduleInverseImage f).obj ((restriction Y).obj F))
        ((moduleInverseImage f).obj ((restriction Y).obj G.obj)) ≫
      restriction_modulePullback f G.obj)

/-- Coefficient ring homomorphism of an étale inverse image at `U`. -/
def etaleCoeffRingHom (f : X ⟶ Y) (U : X.totalᵒᵖ) :
    ((commEtaleStructureSheaf X).obj.obj U : Type u) →+*
      ((commEtaleStructureSheaf Y).obj.obj ((toFunctor f).op.obj U) : Type u) :=
  ((commEtaleStructureSheafIso f).inv.hom.app U).hom

/-- Identity-on-carriers comparison from restriction of scalars of a `Y`-module
at `f(U)` to the inverse-image sections at `U`. -/
def moduleInverseImage_restrictScalars (f : X ⟶ Y) (H : etaleModules Y)
    (U : X.totalᵒᵖ) :
    (ModuleCat.restrictScalars (etaleCoeffRingHom f U)).obj
        (H.val.obj ((toFunctor f).op.obj U)) ⟶
      ((moduleInverseImage f).obj H).val.obj U :=
  moduleCatOfFun _ _ id

/-- Inverse of `moduleInverseImage_restrictScalars`. -/
def moduleInverseImage_restrictScalars_inv (f : X ⟶ Y) (H : etaleModules Y)
    (U : X.totalᵒᵖ) :
    ((moduleInverseImage f).obj H).val.obj U ⟶
      (ModuleCat.restrictScalars (etaleCoeffRingHom f U)).obj
        (H.val.obj ((toFunctor f).op.obj U)) :=
  moduleCatOfFun _ _ id

/-- Sectionwise lax-monoidal comparison
`(f^* H)(U) ⊗ (f^* F)(U) ⟶ f^*(H ⊗ F)(U)`. -/
def moduleInverseImage_tensorComparison_app (f : X ⟶ Y) (H F : etaleModules Y)
    (U : X.totalᵒᵖ) :
    (PresheafOfModules.Monoidal.tensorObj
        ((moduleInverseImage f).obj H).val
        ((moduleInverseImage f).obj F).val).obj U ⟶
      ((moduleInverseImage f).obj (moduleTensorEtale H F)).val.obj U :=
  tensorHom (moduleInverseImage_restrictScalars_inv f H U)
      (moduleInverseImage_restrictScalars_inv f F U) ≫
    μ (ModuleCat.restrictScalars (etaleCoeffRingHom f U))
      (H.val.obj ((toFunctor f).op.obj U))
      (F.val.obj ((toFunctor f).op.obj U)) ≫
    (ModuleCat.restrictScalars (etaleCoeffRingHom f U)).map
      ((moduleSheafificationUnitToVal.{u + 1, u, u, u}
            (commEtaleStructureSheaf Y)
            (PresheafOfModules.Monoidal.tensorObj H.val F.val)).app
          ((toFunctor f).op.obj U) ≫
        (etalePointwiseTensorSheafify_iso H F).hom.val.app
          ((toFunctor f).op.obj U)) ≫
    moduleInverseImage_restrictScalars f (moduleTensorEtale H F) U

/-- Presheaf-level comparison from the pointwise tensor of inverse images to
the inverse image of the tensor. -/
def moduleInverseImage_tensorPresheaf (f : X ⟶ Y) (H F : etaleModules Y) :
    PresheafOfModules.Monoidal.tensorObj
        ((moduleInverseImage f).obj H).val
        ((moduleInverseImage f).obj F).val ⟶
      ((moduleInverseImage f).obj (moduleTensorEtale H F)).val where
  app U := moduleInverseImage_tensorComparison_app f H F U
  naturality := sorry

/-- Canonical comparison `f^* H ⊗ f^* F ⟶ f^*(H ⊗ F)` of étale modules. -/
def moduleInverseImage_tensorComparison (f : X ⟶ Y) (H F : etaleModules Y) :
    moduleTensorEtale ((moduleInverseImage f).obj H)
      ((moduleInverseImage f).obj F) ⟶
      (moduleInverseImage f).obj (moduleTensorEtale H F) :=
  (etalePointwiseTensorSheafify_iso ((moduleInverseImage f).obj H)
      ((moduleInverseImage f).obj F)).inv ≫
    (moduleSheafificationHomEquiv.{u + 1, u, u, u} (commEtaleStructureSheaf X)
        (PresheafOfModules.Monoidal.tensorObj
          ((moduleInverseImage f).obj H).val
          ((moduleInverseImage f).obj F).val)
        ((moduleInverseImage f).obj (moduleTensorEtale H F))).symm
      (moduleInverseImage_tensorPresheaf f H F)

/-- Comparison `f^* SheafHom(F, G) ⟶ SheafHom(f^* F, f^* G)` of étale modules. -/
def moduleSheafHomOnEtale_pullback (f : X ⟶ Y) (F G : etaleModules Y)
    [F.IsFinitePresentation] :
    (moduleInverseImage f).obj (moduleSheafHomOnEtale F G) ⟶
      moduleSheafHomOnEtale ((moduleInverseImage f).obj F)
        ((moduleInverseImage f).obj G) :=
  (moduleSheafHomOnEtale_homEquiv ((moduleInverseImage f).obj F)
      ((moduleInverseImage f).obj G)
      ((moduleInverseImage f).obj (moduleSheafHomOnEtale F G))).symm
    (moduleInverseImage_tensorComparison f (moduleSheafHomOnEtale F G) F ≫
      (moduleInverseImage f).map (moduleSheafHomOnEtale_ev F G))

/-- Comparison
`f^* SheafHom(F, G) ⟶ SheafHom(f^* F, f^* G)` in `LQCoh^{fbc}`, as the étale
sheaf-Hom comparison packaged by `homMk`. -/
def moduleSheafHomLQCohFbc_pullback (f : X ⟶ Y) (F : fppfModules Y) (G : QCoh Y)
    [F.IsFinitePresentation] :
    (LQCohFbc.inverseImage f).obj (moduleSheafHomLQCohFbc F G) ⟶
      moduleSheafHomLQCohFbc ((modulePullback f).obj F)
        ((QCoh.pullback f).obj G) :=
  homMk
    (moduleSheafHomOnEtale_pullback f ((restriction Y).obj F)
        ((restriction Y).obj G.obj) ≫
      moduleSheafHomOnEtale_restrictionPullback f F G)

namespace QCoh

/-- Canonical comparison
`f^* hom(F, G) ⟶ hom(f^* F, f^* G)` of quasi-coherent modules, as the composite
of `LQCohFbc.toQCoh_pullback` with `Q` of the étale sheaf-Hom comparison. -/
def internalHomFP_pullback (f : X ⟶ Y) [AlgebraicStack.Flat f]
    (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation] :
    (pullback f).obj (internalHomFP F G) ⟶
      internalHomFP ((modulePullback f).obj F) ((pullback f).obj G) :=
  (LQCohFbc.toQCoh_pullback f).app (moduleSheafHomLQCohFbc F G) ≫
    (LQCohFbc.toQCoh X).map (moduleSheafHomLQCohFbc_pullback f F G)

/-- For a flat morphism of algebraic stacks, the comparison
`f^* hom(F, G) ⟶ hom(f^* F, f^* G)` is an isomorphism. -/
instance internalHomFP_pullback_isIso (f : X ⟶ Y) [AlgebraicStack.Flat f]
    (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation] :
    IsIso (internalHomFP_pullback f F G) :=
  sorry

/-- Lemma 103.10.9: if `f : X ⟶ Y` is a flat morphism of algebraic stacks, `F`
is an `𝒪_Y`-module of finite presentation and `G` is a quasi-coherent
`𝒪_Y`-module, then `f^* hom(F, G) = hom(f^* F, f^* G)`, where `hom` is
`QCoh.internalHomFP` from Lemma 103.10.8, `f^*` on quasi-coherent modules is
`QCoh.pullback`, and `f^*` on the finitely presented module is
`modulePullback`. -/
@[stacks 0GQP]
def internalHomFP_pullbackIso (f : X ⟶ Y) [AlgebraicStack.Flat f]
    (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation] :
    (pullback f).obj (internalHomFP F G) ≅
      internalHomFP ((modulePullback f).obj F) ((pullback f).obj G) :=
  asIso (internalHomFP_pullback f F G)

/-- The forward map of `internalHomFP_pullbackIso` is the named comparison
`internalHomFP_pullback`. -/
theorem internalHomFP_pullbackIso_hom (f : X ⟶ Y) [AlgebraicStack.Flat f]
    (F : fppfModules Y) (G : QCoh Y) [F.IsFinitePresentation] :
    (internalHomFP_pullbackIso f F G).hom = internalHomFP_pullback f F G :=
  rfl

end QCoh

end AlgebraicGeometry.GroupoidsOver
