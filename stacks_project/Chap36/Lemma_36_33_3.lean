module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.CountableGeneration
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u

/- Lemma 36.33.3: an object of `D_QCoh(𝒪_X)` is a sequential homotopy colimit
of perfect objects of `D(𝒪_X)` if and only if all of its cohomology sheaves have
countable sections on every affine open. -/
@[stacks 0CRQ] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.perfectHomotopyColimit_iff_countableAffineSections :
    ∀ {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
      (hX : ∀ U : X.affineOpens, Countable Γ(X, U))
      (K : AlgebraicGeometry.Scheme.ModuleDerived.Quasicoherent X),
      sequentialHomotopyColimits
        (fun E : RingedSpace.ModuleDerived X.toRingedSpace ↦
          RingedSpace.ModuleDerived.IsPerfect E) K.obj ↔
        ∀ i : ℤ, ∀ U : X.affineOpens,
          Countable (RingedSpace.moduleSectionsOnOpen
            (RingedSpace.ModuleDerived.cohomologySheaf K.obj i) (U : X.Opens)))
