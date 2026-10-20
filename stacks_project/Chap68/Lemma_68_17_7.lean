module

public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PullbackConditions
import StacksCheckRecall

/-!
# Fibre products of decent, reasonable, and property (β) algebraic spaces

If `X` and `Z` are decent, reasonable, or have property (β), then the fibre
product of morphisms `f : X ⟶ Y` and `g : Z ⟶ Y` of algebraic spaces has the
same object property. No hypothesis is imposed on `Y`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

/- Lemma 68.17.7 (1): If `X` and `Z` are decent algebraic spaces over a scheme `S`,
then the fibre product `pullback f g` of morphisms `f : X ⟶ Y` and `g : Z ⟶ Y` is
decent. -/
@[stacks 0ABZ] #check (AlgebraicGeometry.AlgebraicSpace.instIsDecent_pullback :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y),
    [AlgebraicSpace.IsDecent X] → [AlgebraicSpace.IsDecent Z] →
      AlgebraicSpace.IsDecent (pullback f g))

/- Lemma 68.17.7 (2): If `X` and `Z` are reasonable algebraic spaces over a scheme
`S`, then the fibre product `pullback f g` of morphisms `f : X ⟶ Y` and
`g : Z ⟶ Y` is reasonable. -/
@[stacks 0ABZ] #check (AlgebraicGeometry.AlgebraicSpace.instIsReasonable_pullback :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y),
    [AlgebraicSpace.IsReasonable X] → [AlgebraicSpace.IsReasonable Z] →
      AlgebraicSpace.IsReasonable (pullback f g))

/- Lemma 68.17.7 (3): If `X` and `Z` have property (β) of Lemma 68.5.1, then the
fibre product `pullback f g` of morphisms `f : X ⟶ Y` and `g : Z ⟶ Y` has
property (β). -/
@[stacks 0ABZ] #check (AlgebraicGeometry.AlgebraicSpace.instHasPropertyBeta_pullback :
  ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Z ⟶ Y),
    [AlgebraicSpace.HasPropertyBeta X] → [AlgebraicSpace.HasPropertyBeta Z] →
      AlgebraicSpace.HasPropertyBeta (pullback f g))

#check (AlgebraicGeometry.AlgebraicSpace.IsDecent.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pX : P ⟶ X} {pZ : P ⟶ Z},
    IsPullback pX pZ f g → [AlgebraicSpace.IsDecent X] →
      [AlgebraicSpace.IsDecent Z] → AlgebraicSpace.IsDecent P)

#check (AlgebraicGeometry.AlgebraicSpace.IsReasonable.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pX : P ⟶ X} {pZ : P ⟶ Z},
    IsPullback pX pZ f g → [AlgebraicSpace.IsReasonable X] →
      [AlgebraicSpace.IsReasonable Z] → AlgebraicSpace.IsReasonable P)

#check (AlgebraicGeometry.AlgebraicSpace.HasPropertyBeta.of_isPullback :
  ∀ {S : Scheme.{u}} {X Y Z P : AlgebraicSpace S}
    {f : X ⟶ Y} {g : Z ⟶ Y} {pX : P ⟶ X} {pZ : P ⟶ Z},
    IsPullback pX pZ f g → [AlgebraicSpace.HasPropertyBeta X] →
      [AlgebraicSpace.HasPropertyBeta Z] → AlgebraicSpace.HasPropertyBeta P)
