module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FiberLimits
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FiberColimits
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.FiberReflectsIso
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.MonoComplement
public import ReasLib.CategoryTheory.Galois.SetValued
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.CategoryTheory.Limits.MorphismProperty
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory

universe u

namespace AlgebraicGeometry.Scheme.FiniteEtale

/-- The finite étale category over a connected scheme is a pre-Galois category. -/
instance preGaloisCategory {X : Scheme.{u}} [ConnectedSpace X] :
    PreGaloisCategory (FiniteEtale X) where
  hasTerminal :=
    (MorphismProperty.Over.mkIdTerminal finiteEtaleMorphism X).hasTerminal
  hasPullbacks := by
    letI : MorphismProperty.HasOfPostcompProperty
        finiteEtaleMorphism finiteEtaleMorphism :=
      { of_postcomp := by
          intro Y Z W f g hg hfg
          letI : IsFinite g := hg.1
          letI : IsFinite (f ≫ g) := hfg.1
          exact ⟨IsFinite.of_comp f g,
            MorphismProperty.of_postcomp (W := @Etale) f g hg.2 hfg.2⟩ }
    exact MorphismProperty.Over.hasPullbacks finiteEtaleMorphism X
  hasFiniteCoproducts := AlgebraicGeometry.Scheme.FiniteEtale.hasFiniteCoproducts
  hasQuotientsByFiniteGroups := fun group _ _ ↦
    { has_colimit := fun F ↦ HasColimit.mk (finiteGroupQuotientCocone F) }
  monoInducesIsoOnDirectSummand :=
    AlgebraicGeometry.Scheme.FiniteEtale.monoInducesIsoOnDirectSummand

variable {X : Scheme.{u}} [ConnectedSpace X] {K : Type u} [Field K] [IsAlgClosed K]

/-- Geometric fibers preserve epimorphisms through their actual pushout desc maps. -/
instance finiteFiber_preservesEpimorphisms (point : Spec (.of K) ⟶ X) :
    Functor.PreservesEpimorphisms (finiteFiber point) := by
  infer_instance

/-- The finite geometric-fiber functor over a connected scheme is a fiber functor. -/
noncomputable instance finiteFiber_isFiberFunctor (point : Spec (.of K) ⟶ X) :
    FiberFunctor (finiteFiber point) where
  preservesTerminalObjects := inferInstance
  preservesPullbacks := inferInstance
  preservesFiniteCoproducts := inferInstance
  preservesEpis := inferInstance
  preservesQuotientsByFiniteGroups := fun group _ _ ↦
    @preservesColimitsOfShape_of_equiv _ _ _ _
      (SingleObj (Shrink.{0} group)) _ (SingleObj group) _
      (Shrink.mulEquiv.{0} (α := group)).toSingleObjEquiv (finiteFiber point)
      (@preservesColimitsOfShapeOfPreservesFiniteColimits _ _ _ _
        (finiteFiber point) inferInstance (SingleObj (Shrink.{0} group)) inferInstance
        (@SingleObj.finCategoryOfFintype (Shrink.{0} group)
          (Fintype.ofFinite _) inferInstance))
  reflectsIsos := inferInstance

/-- The finite étale category over a connected scheme is a Galois category. -/
instance galoisCategory {X : Scheme.{u}} [ConnectedSpace X] :
    GaloisCategory (FiniteEtale X) where
  toPreGaloisCategory := inferInstance
  hasFiberFunctor := by
    classical
    let x : X := Classical.choice inferInstance
    let Ω := AlgebraicClosure (X.residueField x)
    let point : Spec (.of Ω) ⟶ X :=
      Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x) Ω)) ≫
        X.fromSpecResidueField x
    exact ⟨finiteFiber point, ⟨inferInstance⟩⟩

/-- The specified set-valued geometric-fiber functor over a connected scheme is Galois. -/
theorem fiber_isGalois (point : Spec (.of K) ⟶ X) :
    Functor.IsGalois (fiber point) := sorry

end AlgebraicGeometry.Scheme.FiniteEtale
