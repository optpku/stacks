/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Dualizing.CohenMacaulay
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpace.ModuleDerived

universe u

/- Lemma 48.23.1: A locally Noetherian scheme with a dualizing complex is
Cohen-Macaulay exactly when the complex is locally concentrated in one degree; the
stalkwise criterion, openness of the Cohen-Macaulay locus, its Cohen-Macaulay open
subscheme, and the connected shift conclusion also hold. -/
@[stacks 0AWT] #check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.cohenMacaulay_iff_isLocallyConcentrated :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      {ω : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω),
      AlgebraicGeometry.Scheme.CohenMacaulay X ↔
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsLocallyConcentrated ω)

#check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.stalk_cohenMacaulay_iff_concentrated :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      {ω : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω) (x : X),
      Module.CohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) ↔
        ∃ n : ℤ, DerivedCategory.concentrated (ModuleCat (X.presheaf.stalk x)) n
          (Stalk.obj ω x))

#check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.isOpen_cohenMacaulayLocus :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      {ω : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω),
      IsOpen (AlgebraicGeometry.Scheme.cohenMacaulayLocus X))

#check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.cohenMacaulayOpen :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      {ω : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω), X.Opens)

#check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.coe_cohenMacaulayOpen :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      {ω : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω),
      (hω.cohenMacaulayOpen : Set X) = AlgebraicGeometry.Scheme.cohenMacaulayLocus X)

#check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.cohenMacaulayOpen_isCohenMacaulay :
    ∀ {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian X]
      {ω : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω),
      AlgebraicGeometry.Scheme.CohenMacaulay hω.cohenMacaulayOpen.toScheme)

#check
  (AlgebraicGeometry.Scheme.IsDualizingComplex.exists_canonicalModule_of_connected :
    ∀ {X : AlgebraicGeometry.Scheme.{u}}
      [AlgebraicGeometry.IsLocallyNoetherian X] [ConnectedSpace X]
      [AlgebraicGeometry.Scheme.CohenMacaulay X]
      {ω : AlgebraicGeometry.RingedSpace.ModuleDerived X.toRingedSpace}
      (hω : AlgebraicGeometry.Scheme.IsDualizingComplex ω),
      ∃ n : ℤ,
        let ωX := AlgebraicGeometry.RingedSpace.ModuleDerived.cohomologySheaf ω n
        ωX.IsCoherent ∧ LocallyRingedSpace.Modules.CohenMacaulay ωX ∧
          Nonempty (ω ≅ ((DerivedCategory.singleFunctor X.Modules 0).obj ωX)⟦-n⟧))
