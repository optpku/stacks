module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced.Singleton
import StacksCheckRecall

/-!
# Reduced singleton algebraic spaces

Reducedness and singletonness are equivalent to the existence of a surjective
flat field-spectrum cover, with or without the locally-of-finite-type condition.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 68.13.2: For an algebraic space Z over a scheme S, the following are
equivalent: Z is reduced and its space of points is a singleton; Z admits a
surjective flat morphism from the spectrum of a field; and Z admits such a
morphism that is moreover locally of finite type. -/
@[stacks 06QW]
#check (AlgebraicGeometry.AlgebraicSpace.isReduced_subsingleton_points_tfae :
  ∀ {S : Scheme.{u}} (Z : AlgebraicSpace S),
    List.TFAE
      [ IsReduced Z ∧ Nonempty (Points Z) ∧ Subsingleton (Points Z)
      , existsSurjectiveFlatSpecField Z
      , existsLocallyOfFiniteTypeSurjectiveFlatSpecField Z ])
