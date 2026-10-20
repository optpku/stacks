module

public import stacks_project.Chap46.Remark_46_5_9_Adjunction
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

variable (S : Scheme.{u}) (τ : StandardTopology)

/- Remark 46.5.9 (1): association gives a functor from quasicoherent modules on
`S` to adequate modules on the big `τ`-site. -/
@[stacks 06VN] #check (SheafOfModules.Adeq.associated S τ :
  Scheme.QCoh S ⥤
    SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
      (@SheafOfModules.affineEvaluationUnderlying S τ))

/- Remark 46.5.9 (2): small-Zariski restriction gives a functor from adequate
modules back to quasicoherent modules on `S`. -/
@[stacks 06VN] #check (SheafOfModules.Adeq.zariskiRestriction S τ :
  SheafOfModules.Adeq ModuleValuedFunctor.tensorExtensionUnderlying
      (@SheafOfModules.affineEvaluationUnderlying S τ) ⥤ Scheme.QCoh S)

/- Remark 46.5.9 (3): association is left adjoint to small-Zariski restriction. -/
@[stacks 06VN] #check (SheafOfModules.Adeq.adjunction S τ :
  SheafOfModules.Adeq.associated S τ ⊣ SheafOfModules.Adeq.zariskiRestriction S τ)

/- Remark 46.5.9 (4): the unit `F ⟶ v.obj (u.obj F)` of this adjunction is an
isomorphism. -/
@[stacks 06VN] #check (SheafOfModules.Adeq.adjunctionUnitIsIso S τ :
  IsIso (SheafOfModules.Adeq.adjunction S τ).unit)
