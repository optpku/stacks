/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.RelativeSpectrum.Construction
import StacksCheckRecall

/-!
# Definition 27.4.5 compatibility entry point

ReasLib models a relative spectrum by explicit scheme and universal-map data,
with its representability and realization conditions kept proposition-valued.
-/

@[expose] public section

universe u

/- Definition 27.4.5: an explicit chosen model of `underline Spec_S(A)`. -/
@[stacks 01LW] #check (AlgebraicGeometry.Scheme.relativeSpec :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
      AlgebraicGeometry.Scheme.{u})

/- The explicit data of a chosen relative-spectrum model. -/
#check
  (AlgebraicGeometry.Scheme.RelativeSpectrumOver :
    {S : AlgebraicGeometry.Scheme.{u}} → S.QcAlgebraUnder → Type (u + 1))

/- Construct a relative-spectrum model from its explicit scheme, structural morphism, and
universal family. -/
#check
  (AlgebraicGeometry.Scheme.RelativeSpectrumOver.ofPoint :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (A : S.QcAlgebraUnder)
      {X : AlgebraicGeometry.Scheme.{u}} (π : X ⟶ S)
      (universalMap : (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj A ⟶
        CategoryTheory.Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap π.toShHom)),
      AlgebraicGeometry.Scheme.RelativeSpectrumOver A)

/- The point of the relative-spectrum functor determined by an explicit model. -/
#check
  (AlgebraicGeometry.Scheme.RelativeSpectrumOver.point :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
      AlgebraicGeometry.Scheme.relativeSpectrumPair A P.scheme)

/- The correctness predicate for an explicit relative-spectrum model. -/
#check
  (AlgebraicGeometry.Scheme.IsRelativeSpectrumOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder},
      AlgebraicGeometry.Scheme.RelativeSpectrumOver A → Prop)

/- The functor point determined by an explicit relative-spectrum model. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpecPoint :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
      AlgebraicGeometry.Scheme.relativeSpectrumPair A
        (AlgebraicGeometry.Scheme.relativeSpec P))

/- The structural morphism of an explicit relative-spectrum model. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpecπ :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
      P.scheme ⟶ S)

/- The universal family of an explicit relative-spectrum model. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpecUniversalFamily :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A),
      (AlgebraicGeometry.Scheme.QcAlgebraUnder.forget S).obj A ⟶
        CategoryTheory.Under.mk
          (AlgebraicGeometry.RingedSpace.Hom.commRingSheafPushforwardMap P.π.toShHom))

/- The chosen point represents the relative-spectrum functor. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpecPoint_isRepresentedBy :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      (AlgebraicGeometry.Scheme.relativeSpectrumFunctor A).IsRepresentedBy
        (AlgebraicGeometry.Scheme.relativeSpecPoint P))

/- The structural morphism realizes the relative spectrum. -/
#check
  (AlgebraicGeometry.Scheme.relativeSpecπ_realizesRelativeSpectrum :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {A : S.QcAlgebraUnder}
      (P : AlgebraicGeometry.Scheme.RelativeSpectrumOver A)
      [AlgebraicGeometry.Scheme.IsRelativeSpectrumOver P],
      AlgebraicGeometry.Scheme.realizesRelativeSpectrum A
        (AlgebraicGeometry.Scheme.relativeSpecπ P))
