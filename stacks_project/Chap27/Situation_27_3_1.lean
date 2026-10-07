module

public import ReasLib.AlgebraicGeometry.Scheme.QuasiCoherentAlgebra.Basic
import StacksCheckRecall

/-!
# Situation 27.3.1 compatibility entry point

The ambient category of quasi-coherent algebra sheaves is neutral infrastructure
owned by ReasLib.
-/

@[expose] public section

universe u

/- Situation 27.3.1: for a scheme `S`, an object of `QcAlgebraUnder S` is a
sheaf of `𝒪_S`-algebras whose underlying `𝒪_S`-module is quasi-coherent. -/
@[stacks 01LM] #check (AlgebraicGeometry.Scheme.QcAlgebraUnder :
  AlgebraicGeometry.Scheme.{u} → Type (u + 1))

#check (AlgebraicGeometry.Scheme.schemeCommRingSheaf :
  (S : AlgebraicGeometry.Scheme.{u}) →
    CategoryTheory.Sheaf (Opens.grothendieckTopology S) CommRingCat.{u})

#check (AlgebraicGeometry.Scheme.qcAlgebraUnderProperty :
  (S : AlgebraicGeometry.Scheme.{u}) →
    CategoryTheory.ObjectProperty
      (CategoryTheory.Under (AlgebraicGeometry.Scheme.schemeCommRingSheaf S)))

#check (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget :
  (S : AlgebraicGeometry.Scheme.{u}) →
    CategoryTheory.Functor (AlgebraicGeometry.Scheme.QcAlgebraUnder S)
      (CategoryTheory.Under (AlgebraicGeometry.Scheme.schemeCommRingSheaf S)))

#check (AlgebraicGeometry.Scheme.QcAlgebraUnder.isQuasicoherent_restrictedUnit :
  (S : AlgebraicGeometry.Scheme.{u}) →
    (A : AlgebraicGeometry.Scheme.QcAlgebraUnder S) →
      ((SheafOfModules.RingedSite.restrictionAlong A.obj.hom).obj
        (SheafOfModules.RingedSite.unitModule
          (Opens.grothendieckTopology S)
          (A.obj.right : CategoryTheory.Sheaf
            (Opens.grothendieckTopology S) CommRingCat.{u}))).IsQuasicoherent)
