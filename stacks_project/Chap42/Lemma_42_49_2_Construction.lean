module

public import ReasLib.AlgebraicGeometry.BivariantClass.PushforwardComp

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass

/- The canonical proper-pushforward composite API: `pushforwardComp`. -/
#check (AlgebraicGeometry.BivariantClass.pushforwardComp :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {E Z W X : Over S} [LocallyOfFiniteType E.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType W.hom] [LocallyOfFiniteType X.hom]
    (e : E ⟶ Z) [IsProper e.left] (i : Z ⟶ X) (j : E ⟶ W) (w : W ⟶ X)
    (factor : j ≫ w = e ≫ i) (p : ℤ) (a : BivariantClass δ j p)
    (c : BivariantClass δ w 0), BivariantClass δ i p)

/- The canonical proper-pushforward composite API: `pushforwardComp_def`. -/
#check (AlgebraicGeometry.BivariantClass.pushforwardComp_def :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {E Z W X : Over S} [LocallyOfFiniteType E.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType W.hom] [LocallyOfFiniteType X.hom]
    (e : E ⟶ Z) [IsProper e.left] (i : Z ⟶ X) (j : E ⟶ W) (w : W ⟶ X)
    (factor : j ≫ w = e ≫ i) (p : ℤ) (a : BivariantClass δ j p)
    (c : BivariantClass δ w 0), pushforwardComp δ e i j w factor p a c =
      properPushforward δ e i p (factor ▸ (Int.add_zero p ▸ comp δ j w a c)))

/- The canonical proper-pushforward composite API: `restrict_pushforwardComp`. -/
#check (AlgebraicGeometry.BivariantClass.restrict_pushforwardComp :
    ∀ {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    {E Z W X E' Z' W' X' : Over S}
    [LocallyOfFiniteType E.hom] [LocallyOfFiniteType Z.hom]
    [LocallyOfFiniteType W.hom] [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType E'.hom] [LocallyOfFiniteType Z'.hom]
    [LocallyOfFiniteType W'.hom] [LocallyOfFiniteType X'.hom]
    (e : E ⟶ Z) [IsProper e.left] (i : Z ⟶ X) (j : E ⟶ W) (w : W ⟶ X)
    (factor : j ≫ w = e ≫ i)
    (e' : E' ⟶ Z') [IsProper e'.left] (i' : Z' ⟶ X')
    (j' : E' ⟶ W') (w' : W' ⟶ X') (factor' : j' ≫ w' = e' ≫ i')
    (gE : E' ⟶ E) (gZ : Z' ⟶ Z) (gW : W' ⟶ W) (gX : X' ⟶ X)
    [LocallyOfFiniteType gW.left] [LocallyOfFiniteType gX.left]
    (squareE : IsPullback gE.left e'.left e.left gZ.left)
    (squareZ : IsPullback gZ.left i'.left i.left gX.left)
    (squareW : IsPullback gW.left w'.left w.left gX.left)
    (squareJ : IsPullback gE.left j'.left j.left gW.left)
    (p : ℤ) (a : BivariantClass δ j p) (c : BivariantClass δ w 0), pushforwardComp δ e' i' j' w' factor' p
        (restrict δ gE j' gW squareJ p a)
        (restrict δ gW w' gX squareW 0 c) =
      restrict δ gZ i' gX squareZ p
        (pushforwardComp δ e i j w factor p a c))

end AlgebraicGeometry.BivariantClass
