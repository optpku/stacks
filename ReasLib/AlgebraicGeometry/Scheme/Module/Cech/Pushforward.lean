module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import ReasLib.Algebra.Homology.CochainComplex.Bounded.ExtendNat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.Topology.Sheaves.Abelian.Sheafification
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cech.Resolution
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pushed-forward Čech resolutions

A finite affine open cover gives a bounded-below complex on the target of a scheme morphism.
The construction is functorial in a quasicoherent module and carries a canonical comparison to
bounded-below derived pushforward.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The canonical Grothendieck-abelian structure on modules over a scheme. -/
@[stacks 01XL "Grothendieck abelian category of scheme modules"]
noncomputable instance instIsGrothendieckAbelian (X : Scheme.{u}) :
    IsGrothendieckAbelian.{u} X.Modules :=
  inferInstanceAs (IsGrothendieckAbelian.{u} (SheafOfModules.{u} X.ringCatSheaf))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.OpenCoverCech

variable {X S : Scheme.{u}} {ι : Type u}

/-- Pushing the module-valued Čech resolution forward termwise gives a functor to complexes on
the target scheme. -/
noncomputable def pushforwardFunctor
    (f : X ⟶ S) (𝒰 : ι → X.Opens) :
    X.Modules ⥤ CochainComplex S.Modules ℕ :=
  openCoverModuleCechComplexFunctor 𝒰 ⋙
    (Scheme.Modules.pushforward f).mapHomologicalComplex (ComplexShape.up ℕ)

/-- The pushed-forward module-valued Čech complex associated to an open family. -/
abbrev pushforward
    (f : X ⟶ S) (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    CochainComplex S.Modules ℕ :=
  (pushforwardFunctor f 𝒰).obj ℱ

/-- The integer-indexed extension of the pushed-forward nonnegative Čech complex. -/
abbrev pushforwardInt
    (f : X ⟶ S) (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    CochainComplex S.Modules ℤ :=
  (pushforward f 𝒰 ℱ).extend ComplexShape.embeddingUpNat

/-- The Čech-resolution functor with its nonnegative complexes extended to bounded-below integer
complexes. -/
noncomputable def plusFunctor
    (𝒰 : ι → X.Opens) : X.Modules ⥤ CochainComplex.Plus X.Modules :=
  openCoverModuleCechComplexFunctor 𝒰 ⋙ CochainComplex.Plus.extendNat X.Modules

/-- The bounded-derived realization of the pushed-forward Čech resolution, functorial on
quasicoherent modules. -/
noncomputable def derivedPushforward
    (f : X ⟶ S) (𝒰 : ι → X.Opens) :
    QCoh X ⥤ DerivedCategory.Plus S.Modules :=
  QCoh.inclusion X ⋙ plusFunctor 𝒰 ⋙
    (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
    HomotopyCategory.Plus.quotient S.Modules ⋙ DerivedCategory.Plus.Qh

/-- Every term of the pushed-forward Čech complex of a quasicoherent module for a finite affine
cover is quasicoherent when the source and target have affine diagonal. -/
theorem pushforward_term_isQuasicoherent
    (f : X ⟶ S)
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    [Finite ι] (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i))
    (ℱ : X.Modules) [ℱ.IsQuasicoherent] (p : ℕ) :
    ((pushforward f 𝒰 ℱ).X p).IsQuasicoherent := sorry

/-- Extending a nonnegative pushed-forward Čech complex to integer degrees is bounded below. -/
theorem pushforwardInt_isBoundedBelow
    (f : X ⟶ S) (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    CochainComplex.plus S.Modules (pushforwardInt f 𝒰 ℱ) := sorry

/-- Localizing the bounded Čech augmentation gives a morphism in the bounded-below derived
category. -/
noncomputable def augmentation
    (𝒰 : ι → X.Opens) (ℱ : X.Modules) :
    (DerivedCategory.Plus.singleFunctor X.Modules 0).obj ℱ ⟶
      DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient X.Modules).obj
          ((plusFunctor 𝒰).obj ℱ)) :=
  (DerivedCategory.Plus.ι).preimage
    ((DerivedCategory.Plus.singleFunctorιIso X.Modules 0).hom.app ℱ ≫
      (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).hom.app ℱ ≫
      DerivedCategory.Q.map
        ((HomologicalComplex.extendSingleIso
            ComplexShape.embeddingUpNat ℱ 0 0 rfl).inv ≫
          HomologicalComplex.extendMap
            ((openCoverModuleCechAugmentation 𝒰).app ℱ)
            ComplexShape.embeddingUpNat) ≫
      (DerivedCategory.quotientCompQhIso X.Modules).inv.app
        ((plusFunctor 𝒰).obj ℱ).obj ≫
      DerivedCategory.Qh.map
        ((HomotopyCategory.Plus.quotientCompιIso X.Modules).inv.app
          ((plusFunctor 𝒰).obj ℱ)) ≫
      (DerivedCategory.Plus.QhCompιIsoιCompQh X.Modules).inv.app
        ((HomotopyCategory.Plus.quotient X.Modules).obj
          ((plusFunctor 𝒰).obj ℱ)))

/-- The localized Čech augmentation of an open cover is invertible. -/
theorem augmentation_isIso
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰) (ℱ : X.Modules) :
    IsIso (augmentation 𝒰 ℱ) := sorry

/-- The quotient comparison for the pushforward of bounded-below complexes. -/
noncomputable def pushforwardQuotientIso (f : X ⟶ S) :
    (Scheme.Modules.pushforward f).mapCochainComplexPlus ⋙
        HomotopyCategory.Plus.quotient S.Modules ≅
      HomotopyCategory.Plus.quotient X.Modules ⋙
        (Scheme.Modules.pushforward f).mapHomotopyCategoryPlus :=
  ((HomotopyCategory.Plus.fullyFaithfulι S.Modules).whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (CochainComplex.Plus.ι X.Modules)
      ((Scheme.Modules.pushforward f).mapHomotopyCategoryFactors
        (ComplexShape.up ℤ)).symm)

/-- The Čech augmentation, regarded as an isomorphism after bounded-below localization. -/
noncomputable def augmentationIso
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰) (ℱ : X.Modules) :
    (DerivedCategory.Plus.singleFunctor X.Modules 0).obj ℱ ≅
      DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.quotient X.Modules).obj ((plusFunctor 𝒰).obj ℱ)) :=
  @asIso _ _ _ _ (augmentation 𝒰 ℱ) (augmentation_isIso 𝒰 h𝒰 ℱ)

/-- The component of the canonical comparison from the pushed-forward Čech resolution to the
bounded-below right-derived pushforward. -/
noncomputable def comparisonApp
    (f : X ⟶ S)
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰) (ℱ : QCoh X) :
    (derivedPushforward f 𝒰).obj ℱ ⟶
      ((QCoh.inclusion X ⋙ DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
        (Scheme.Modules.pushforward f).rightDerivedFunctorPlus).obj ℱ) := by
  exact
    DerivedCategory.Plus.Qh.map
        ((pushforwardQuotientIso f).hom.app ((plusFunctor 𝒰).obj ℱ.obj)) ≫
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app
        ((HomotopyCategory.Plus.quotient X.Modules).obj
          ((plusFunctor 𝒰).obj ℱ.obj)) ≫
      (Scheme.Modules.pushforward f).rightDerivedFunctorPlus.map
        (augmentationIso 𝒰 h𝒰 ℱ.obj).inv

/-- The components of the Čech-to-derived-pushforward comparison are natural in quasicoherent
modules. -/
theorem comparison_naturality
    (f : X ⟶ S)
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    {ℱ 𝒢 : QCoh X} (φ : ℱ ⟶ 𝒢) :
    (derivedPushforward f 𝒰).map φ ≫
        comparisonApp f 𝒰 h𝒰 𝒢 =
      comparisonApp f 𝒰 h𝒰 ℱ ≫
        (QCoh.inclusion X ⋙ DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
          (Scheme.Modules.pushforward f).rightDerivedFunctorPlus).map φ := sorry

/-- The canonical comparison from the pushed-forward Čech resolution to bounded-below derived
pushforward, natural in the quasicoherent module. -/
noncomputable def comparison
    (f : X ⟶ S)
    (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰) :
    derivedPushforward f 𝒰 ⟶
      QCoh.inclusion X ⋙ DerivedCategory.Plus.singleFunctor X.Modules 0 ⋙
        (Scheme.Modules.pushforward f).rightDerivedFunctorPlus where
  app ℱ := comparisonApp f 𝒰 h𝒰 ℱ
  naturality _ _ φ := comparison_naturality f 𝒰 h𝒰 φ

/-- For a finite affine cover and affine diagonals, the canonical Čech comparison is invertible. -/
@[stacks 01XL]
theorem comparison_isIso
    (f : X ⟶ S)
    [IsAffineHom (pullback.diagonal (terminal.from X))]
    [IsAffineHom (pullback.diagonal (terminal.from S))]
    [Finite ι] (𝒰 : ι → X.Opens) (h𝒰 : IsOpenCover 𝒰)
    (h𝒰_affine : ∀ i, IsAffineOpen (𝒰 i)) :
    IsIso (comparison f 𝒰 h𝒰) := sorry

end AlgebraicGeometry.Scheme.OpenCoverCech
