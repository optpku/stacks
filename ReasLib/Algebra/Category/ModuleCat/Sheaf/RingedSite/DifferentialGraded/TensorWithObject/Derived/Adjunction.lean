module

public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.DifferentialGraded.Representable.Derived
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Adjunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.TensorWithObject.Derived.Functor

/-!
# Derived tensor-representable adjunction on a ringed site

This file specializes the generic derived enriched representable functor to complexes of module
sheaves and derives the tensor-representable adjunction.  The local abbreviations fix the canonical
ringed-site localization and quasi-isomorphism class; the generic representable module remains the
owner of the derived functor and its unit.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory
open CategoryTheory.CochainComplex.Enriched
open DifferentialGradedCategory
open scoped DifferentialGradedCategory

namespace SheafOfModules.RingedSite.TensorWithObject.Derived

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v} RingCat.{max u v})]
variable {O : Sheaf J CommRingCat.{max u v}}

/-- K-injective resolutions define the ordinary underlying right-derived representable
functor; the generic representable API then lifts definedness to enriched DG modules. -/
@[stacks 09LY "definedness of the derived representable functor"]
instance hasUnderlyingRepresentableFunctor
    (K : Complex (J := J) (O := O)) :
    DifferentialGradedCategory.Representable.HasUnderlyingDerivedFunctor
      K quasiIso := sorry

/-- The total right derived enriched representable functor `RHom(K, -)`. -/
@[stacks 09LY "derived representable functor"]
noncomputable abbrev representableFunctor (K : Complex (J := J) (O := O)) :
    RingedSiteDerived.max J O ⥤
      DifferentialGradedModule.Derived.Category (endDGA K) :=
  DifferentialGradedCategory.Representable.derivedFunctor K derivedQ quasiIso

/-- The canonical comparison from homotopy-level representable Hom to `RHom(K, -)`. -/
@[stacks 09LY "derived representable comparison transformation"]
noncomputable abbrev representableUnit (K : Complex (J := J) (O := O)) :
    DifferentialGradedCategory.Representable.sourceFunctor K ⟶
      derivedQ ⋙ representableFunctor K :=
  DifferentialGradedCategory.Representable.derivedUnit K derivedQ quasiIso

/-- The composite with `RHom(K, -)` retains the absolute left-derived universal property
needed to derive the tensor-Hom adjunction. -/
@[stacks 09LY "left-derived property of tensor followed by representable"]
instance tensorRepresentable_isLeftDerived
    (K : Complex (J := J) (O := O)) :
    (tensorFunctor K ⋙ representableFunctor K).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫
        Functor.whiskerRight (tensorCounit K) (representableFunctor K))
      (DifferentialGradedModule.quasiIso (endDGA K)) := sorry

/-- The composite with derived tensor retains the absolute right-derived universal property
needed to derive the tensor-Hom adjunction. -/
@[stacks 09LY "right-derived property of representable followed by tensor"]
instance representableTensor_isRightDerived
    (K : Complex (J := J) (O := O)) :
    (representableFunctor K ⋙ tensorFunctor K).IsRightDerivedFunctor
      (Functor.whiskerRight (representableUnit K) (tensorFunctor K) ≫
        (Functor.associator _ _ _).hom)
      quasiIso := sorry

/-- Lemma 22.35.5 (09LY): derived tensoring with `K` is left adjoint to the derived
representable functor `RHom(K, -)`. -/
@[stacks 09LY "derived tensor-representable adjunction on a ringed site"]
noncomputable def adjunction (K : Complex (J := J) (O := O)) :
    tensorFunctor K ⊣ representableFunctor K :=
  (TensorWithObject.homotopyAdjunction K).derived
    (DifferentialGradedModule.quasiIso (endDGA K))
    quasiIso
    (tensorCounit K) (representableUnit K)

/-- The derived tensor functor is recognized as a left adjoint. -/
@[stacks 09LY "left-adjoint instance for derived tensor"]
noncomputable instance tensorFunctor_isLeftAdjoint
    (K : Complex (J := J) (O := O)) :
    (tensorFunctor K).IsLeftAdjoint :=
  (adjunction K).isLeftAdjoint

/-- The derived representable functor is recognized as a right adjoint. -/
@[stacks 09LY "right-adjoint instance for derived representable"]
noncomputable instance representableFunctor_isRightAdjoint
    (K : Complex (J := J) (O := O)) :
    (representableFunctor K).IsRightAdjoint :=
  (adjunction K).isRightAdjoint

/-- The bifunctorial Hom equivalence of the concrete derived tensor-representable
adjunction. -/
@[stacks 09LY "derived tensor-representable Hom equivalence"]
noncomputable def homEquiv (K : Complex (J := J) (O := O))
    (M : DifferentialGradedModule.Derived.Category (endDGA K))
    (L : RingedSiteDerived.max J O) :
    ((tensorFunctor K).obj M ⟶ L) ≃ (M ⟶ (representableFunctor K).obj L) :=
  (adjunction K).homEquiv M L

end SheafOfModules.RingedSite.TensorWithObject.Derived
