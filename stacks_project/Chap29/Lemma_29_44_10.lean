module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiFinite
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

variable {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
  [AlgebraicGeometry.IsFinite f]

/- Lemma 29.44.10: a finite morphism is quasi-finite. -/
@[stacks 02NU] #check (AlgebraicGeometry.Scheme.Hom.instQuasiFinite f :
  AlgebraicGeometry.Scheme.Hom.QuasiFinite f)
