module

public import ReasLib.AlgebraicGeometry.Scheme.Module.FinitePresentation.Relative.Comparison
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

/- Lemma 37.58.3 (1): over a locally finitely presented morphism, relative finite
presentation and ordinary finite presentation agree for a quasi-coherent module. -/
@[stacks 09T8] #check
  (AlgebraicGeometry.Scheme.Modules.isFinitePresentationOver_iff_isFinitePresentation :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
      (F : X.Modules) [F.IsQuasicoherent],
      F.IsFinitePresentationOver f ↔ F.IsFinitePresentation)

/- Lemma 37.58.3 (2): a locally finite type morphism is locally of finite presentation
exactly when its structure sheaf is of finite presentation relative to the base. -/
@[stacks 09T8] #check
  (AlgebraicGeometry.Scheme.Modules.locallyOfFinitePresentation_iff_structureSheaf_isFinitePresentationOver :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f],
      LocallyOfFinitePresentation f ↔
        AlgebraicGeometry.Scheme.Modules.IsFinitePresentationOver
          (SheafOfModules.unit X.ringCatSheaf : X.Modules) f)
