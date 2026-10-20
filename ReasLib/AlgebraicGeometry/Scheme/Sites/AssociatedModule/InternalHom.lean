/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pullback.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.InternalHom
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule.Tensor

/-!
# Internal Hom of associated modules

This module constructs the canonical comparison morphisms from associated
modules of scheme-level internal Homs to internal Homs of associated modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- The internal Hom of quasi-coherent scheme modules, bundled using finite
presentation of its source. -/
noncomputable def quasicoherentInternalHom
    (S : Scheme.{u}) (F G : Scheme.QCoh S) (hF : F.obj.IsFinitePresentation) :
    Scheme.QCoh S :=
  ⟨Scheme.Modules.internalHom F.obj G.obj,
    @Scheme.Modules.isQuasicoherent_internalHom S F.obj G.obj hF G.property⟩

/-- The underlying module of the bundled quasi-coherent internal Hom is the
scheme-level internal Hom. -/
theorem quasicoherentInternalHom_obj
    (S : Scheme.{u}) (F G : Scheme.QCoh S) (hF : F.obj.IsFinitePresentation) :
    (quasicoherentInternalHom S F G hF).obj =
      Scheme.Modules.internalHom F.obj G.obj := sorry

/-- Evaluation from the tensor product with a scheme-level internal Hom. -/
noncomputable def internalHomEvaluation
    (S : Scheme.{u}) (F G : Scheme.QCoh S) (hF : F.obj.IsFinitePresentation) :
    quasicoherentTensor S F (quasicoherentInternalHom S F G hF) ⟶ G :=
  ⟨(ihom.ev F.obj).app G.obj⟩

/-- The comparison from the commutative presentation of a small-site associated
module of scheme internal Hom to internal Hom of the associated modules. -/
noncomputable def smallInternalHomComparison
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    StandardSmall.comm τ S (quasicoherentInternalHom S F G hF).obj ⟶
      (ihom (StandardSmall.comm τ S F.obj)).obj
        (StandardSmall.comm τ S G.obj) :=
  MonoidalClosed.curry
    (smallTensorComparison S τ F (quasicoherentInternalHom S F G hF) ≫
      (smallModuleLift S τ).map
        ((smallModuleFunctor S τ).map (internalHomEvaluation S F G hF)))

/-- Uncurrying the small-site internal-Hom comparison recovers its
tensor-evaluation map. -/
theorem uncurry_smallInternalHomComparison
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    MonoidalClosed.uncurry (smallInternalHomComparison S τ F G hF) =
      smallTensorComparison S τ F (quasicoherentInternalHom S F G hF) ≫
        (smallModuleLift S τ).map
          ((smallModuleFunctor S τ).map (internalHomEvaluation S F G hF)) := sorry

/-- The comparison from the commutative presentation of a big-site associated
module of scheme internal Hom to internal Hom of the associated modules. -/
noncomputable def bigInternalHomComparison
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    bigComm τ S (quasicoherentInternalHom S F G hF).obj ⟶
      (ihom (bigComm τ S F.obj)).obj (bigComm τ S G.obj) :=
  MonoidalClosed.curry
    (bigTensorComparison S τ F (quasicoherentInternalHom S F G hF) ≫
      (bigModuleLift S τ).map
        ((bigModuleFunctor S τ).map (internalHomEvaluation S F G hF)))

/-- Uncurrying the big-site internal-Hom comparison recovers its
tensor-evaluation map. -/
theorem uncurry_bigInternalHomComparison
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    MonoidalClosed.uncurry (bigInternalHomComparison S τ F G hF) =
      bigTensorComparison S τ F (quasicoherentInternalHom S F G hF) ≫
        (bigModuleLift S τ).map
          ((bigModuleFunctor S τ).map (internalHomEvaluation S F G hF)) := sorry

/-- The internal-Hom comparison for ordinary small-standard-site associated
modules, displayed after the conservative universe lift. -/
noncomputable def smallModuleInternalHomComparison
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    (smallModuleLift S τ).obj
        ((smallModuleFunctor S τ).obj (quasicoherentInternalHom S F G hF)) ⟶
      (ihom ((smallModuleLift S τ).obj ((smallModuleFunctor S τ).obj F))).obj
        ((smallModuleLift S τ).obj ((smallModuleFunctor S τ).obj G)) :=
  (smallModuleLiftIso S τ (quasicoherentInternalHom S F G hF)).hom ≫
    smallInternalHomComparison S τ F G hF ≫
      (MonoidalClosed.pre (smallModuleLiftIso S τ F).hom).app
        (StandardSmall.comm τ S G.obj) ≫
        (ihom ((smallModuleLift S τ).obj ((smallModuleFunctor S τ).obj F))).map
          (smallModuleLiftIso S τ G).inv

/-- Invertibility of the ordinary small-site internal-Hom comparison is
equivalent to invertibility of its commutative presentation. -/
theorem smallModuleInternalHomComparison_isIso_iff
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    IsIso (smallModuleInternalHomComparison S τ F G hF) ↔
      IsIso (smallInternalHomComparison S τ F G hF) := sorry

/-- The internal-Hom comparison for ordinary big-site associated modules,
displayed after the conservative universe lift. -/
noncomputable def bigModuleInternalHomComparison
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    (bigModuleLift S τ).obj
        ((bigModuleFunctor S τ).obj (quasicoherentInternalHom S F G hF)) ⟶
      (ihom ((bigModuleLift S τ).obj ((bigModuleFunctor S τ).obj F))).obj
        ((bigModuleLift S τ).obj ((bigModuleFunctor S τ).obj G)) :=
  (bigModuleLiftIso S τ (quasicoherentInternalHom S F G hF)).hom ≫
    bigInternalHomComparison S τ F G hF ≫
      (MonoidalClosed.pre (bigModuleLiftIso S τ F).hom).app
        (bigComm τ S G.obj) ≫
        (ihom ((bigModuleLift S τ).obj ((bigModuleFunctor S τ).obj F))).map
          (bigModuleLiftIso S τ G).inv

/-- Invertibility of the ordinary big-site internal-Hom comparison is
equivalent to invertibility of its commutative presentation. -/
theorem bigModuleInternalHomComparison_isIso_iff
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    IsIso (bigModuleInternalHomComparison S τ F G hF) ↔
      IsIso (bigInternalHomComparison S τ F G hF) := sorry

/-- Failure of the ordinary big-site internal-Hom comparison is equivalent to
failure of its commutative presentation. -/
theorem bigModuleInternalHomComparison_not_isIso_iff
    (S : Scheme.{u}) (τ : StandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    ¬ IsIso (bigModuleInternalHomComparison S τ F G hF) ↔
      ¬ IsIso (bigInternalHomComparison S τ F G hF) := sorry

/-- On a small Zariski or étale site, the internal-Hom comparison is invertible
when the source module is finitely presented. -/
instance smallInternalHomComparisonIsIso
    (S : Scheme.{u}) (τ : SmallStandardTopology) (F G : Scheme.QCoh S)
    (hF : F.obj.IsFinitePresentation) :
    IsIso (smallModuleInternalHomComparison S τ.toStandard F G hF) := sorry

end AlgebraicGeometry.Scheme.AssociatedModule
