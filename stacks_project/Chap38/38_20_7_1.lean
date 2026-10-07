module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.Scheme.BaseChange.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.LocallyFree.Pointwise
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

variable {X S : Scheme.{u}} (f : X ⟶ S) [Smooth f] [GeometricallyIrreducible f]
  (ℱ : X.Modules) [ℱ.IsQuasicoherent] [ℱ.IsFiniteType] (p : ℕ)
  (T : Over S) (t : T.left)

/- 38.20.7.1: the base change of `ℱ` is free of rank `p` on an open neighbourhood of the
image of the generic point of the fibre over `t`. -/
@[stacks 05MQ] #check
  (SheafOfModules.IsFreeOfRankAt p (Scheme.Modules.baseChangeModule f T.hom ℱ)
    ((pullback.snd f T.hom).fiberι t
      (genericPoint ((pullback.snd f T.hom).fiber t))) : Prop)
