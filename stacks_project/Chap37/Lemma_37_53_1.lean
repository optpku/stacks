module

public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein
import StacksCheckRecall

open AlgebraicGeometry CategoryTheory Limits

universe u

/- Lemma 37.53.1: the relative normalization of a universally closed, quasi-separated morphism
realizes the relative spectrum of its pushed-forward structure sheaf. -/
@[stacks 03GY] #check
  (AlgebraicGeometry.Scheme.Hom.fromNormalization_realizesRelativeSpectrum :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [QuasiSeparated f] [UniversallyClosed f],
      Scheme.realizesRelativeSpectrum
        (Scheme.pushforwardStructureSheafQcAlgebra f) f.fromNormalization)

section

variable {X S S' : Scheme.{u}} (f : X ⟶ S) [QuasiSeparated f] [UniversallyClosed f]

/- The canonical maps through the relative normalization factor `f`. -/
#check
  (AlgebraicGeometry.Scheme.Hom.toNormalization_fromNormalization f :
    f.toNormalization ≫ f.fromNormalization = f)

/- The map to the relative normalization is universally closed. -/
#check
  (AlgebraicGeometry.instUniversallyClosedToNormalization f :
    UniversallyClosed f.toNormalization)

/- The map to the relative normalization is quasi-compact. -/
#check
  (AlgebraicGeometry.Scheme.Hom.instQuasiCompactToNormalization f :
    QuasiCompact f.toNormalization)

/- The map to the relative normalization is quasi-separated. -/
#check
  (AlgebraicGeometry.Scheme.Hom.instQuasiSeparatedToNormalization f :
    QuasiSeparated f.toNormalization)

/- The map to the relative normalization is surjective. -/
#check
  (AlgebraicGeometry.Surjective.of_universallyClosed_of_isDominant f.toNormalization :
    Surjective f.toNormalization)

/- The structural morphism from the relative normalization is integral. -/
#check
  (AlgebraicGeometry.Scheme.Hom.instIsIntegralHomFromNormalization f :
    IsIntegralHom f.fromNormalization)

/- The structure-sheaf map for the morphism to the relative normalization is an isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.Hom.instIsIsoPushforwardMapToNormalization f :
    IsIso (RingedSpace.Hom.commRingSheafPushforwardMap f.toNormalization.toShHom))

variable (g : S' ⟶ S) [Flat g]

/- The canonical normalization comparison after flat base change is an isomorphism. -/
#check
  (AlgebraicGeometry.Scheme.Hom.instIsIsoNormalizationPullbackOfFlat f g :
    IsIso (f.normalizationPullback g))

/- The normalization comparison is compatible with the structural morphisms. -/
#check
  (AlgebraicGeometry.Scheme.Hom.normalizationPullback_snd f g :
    f.normalizationPullback g ≫ pullback.snd f.fromNormalization g =
      (pullback.snd f g).fromNormalization)

/- The normalization comparison is compatible with the maps from the pulled-back source. -/
#check
  (AlgebraicGeometry.Scheme.Hom.toNormalization_normalizationPullback_fst f g :
    (pullback.snd f g).toNormalization ≫ f.normalizationPullback g ≫
        pullback.fst f.fromNormalization g =
      pullback.fst f g ≫ f.toNormalization)

end
