module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.FinitePresentation
import StacksCheckRecall

universe u

/- Lemma 28.22.6: every quasi-coherent module on a quasi-compact quasi-separated scheme is a
filtered colimit of finitely presented modules. -/
@[stacks 01PJ] #check
  (AlgebraicGeometry.Scheme.Modules.isFinitePresentation_ind :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (F : X.Modules) [F.IsQuasicoherent],
      (SheafOfModules.isFinitePresentation X.ringCatSheaf).ind.{u} F)
