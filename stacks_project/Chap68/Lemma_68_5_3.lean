module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RepresentableConditions
import StacksCheckRecall

/-!
# Inheritance of conditions along representable morphisms

If `f : X ⟶ Y` is a representable morphism of algebraic spaces over a scheme `S`
and `Y` has one of the properties (β), (γ), (δ), (ε), or (θ) of Lemma 68.5.1,
then `X` has the same property.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 68.5.3 (1): Let `S` be a scheme. If `f : X ⟶ Y` is a representable
morphism of algebraic spaces over `S` and `Y` has property (β), then `X` has
property (β). -/
@[stacks 03KF] #check
  (AlgebraicGeometry.AlgebraicSpace.HasPropertyBeta.of_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f) [HasPropertyBeta Y], HasPropertyBeta X)

/- Lemma 68.5.3 (2): Let `S` be a scheme. If `f : X ⟶ Y` is a representable
morphism of algebraic spaces over `S` and `Y` is decent, then `X` is decent. -/
@[stacks 03KF] #check
  (AlgebraicGeometry.AlgebraicSpace.IsDecent.of_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f) [IsDecent Y], IsDecent X)

/- Lemma 68.5.3 (3): Let `S` be a scheme. If `f : X ⟶ Y` is a representable
morphism of algebraic spaces over `S` and `Y` is reasonable, then `X` is
reasonable. -/
@[stacks 03KF] #check
  (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f) [IsReasonable Y], IsReasonable X)

/- Lemma 68.5.3 (4): Let `S` be a scheme. If `f : X ⟶ Y` is a representable
morphism of algebraic spaces over `S` and `Y` is very reasonable, then `X` is
very reasonable. -/
@[stacks 03KF] #check
  (AlgebraicGeometry.AlgebraicSpace.IsVeryReasonable.of_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f) [IsVeryReasonable Y], IsVeryReasonable X)

/- Lemma 68.5.3 (5): Let `S` be a scheme. If `f : X ⟶ Y` is a representable
morphism of algebraic spaces over `S` and `Y` is a scheme, then `X` is a scheme. -/
@[stacks 03KF] #check
  (AlgebraicGeometry.AlgebraicSpace.IsScheme.of_relativelyRepresentable :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      (hf : yoneda.relativelyRepresentable f) [IsScheme Y], IsScheme X)

end AlgebraicGeometry.AlgebraicSpace
