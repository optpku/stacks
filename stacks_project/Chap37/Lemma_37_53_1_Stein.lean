module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.fromNormalization_realizesRelativeSpectrum :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiSeparated f] [AlgebraicGeometry.UniversallyClosed f],
      AlgebraicGeometry.Scheme.realizesRelativeSpectrum
        (AlgebraicGeometry.Scheme.pushforwardStructureSheafQcAlgebra f) f.fromNormalization)

#check
  (AlgebraicGeometry.Scheme.Hom.instIsIsoPushforwardMapToNormalization :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.QuasiSeparated f] [AlgebraicGeometry.UniversallyClosed f],
      IsIso (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap
        f.toNormalization.toShHom))

#check
  (AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfFlat :
    ∀ {X S S' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
      [AlgebraicGeometry.QuasiSeparated f] [AlgebraicGeometry.UniversallyClosed f]
      [AlgebraicGeometry.Flat g],
      IsIso (f.normalizationPullback g))
