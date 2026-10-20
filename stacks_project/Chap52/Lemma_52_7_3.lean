module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Completion.FormalFunctions
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion

universe u

/- Lemma 52.7.3 (1): for a Noetherian ring `A`, a Noetherian scheme `X` over
`Spec A`, and a coherent module `F` with finite cohomology in every degree,
the `I`-adic completion of cohomology fits into the Milnor short exact sequence
with the positive quotient cohomology tower. -/
@[stacks 0A0M] #check (AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion.cohomologyShortExact :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A)) (I : Ideal A) (F : X.Modules) [F.IsCoherent]
    (hfinite : ∀ q : ℤ,
      Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
          ((Scheme.FlatPullbackSections.baseSections f).obj
            ((ModuleCech.moduleToDerived X).obj F))))
    (p : ℤ),
    ∃ (ι :
        (quotientCohomologySystem f I F (p - 1)).firstDerivedLimit ⟶
          ModuleCat.of A
            (AdicCompletion I
              (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
                ((Scheme.FlatPullbackSections.baseSections f).obj
                  ((ModuleCech.moduleToDerived X).obj F)) : Type u))))
      (π :
        ModuleCat.of A
            (AdicCompletion I
              (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) p).obj
                ((Scheme.FlatPullbackSections.baseSections f).obj
                  ((ModuleCech.moduleToDerived X).obj F)) : Type u))) ⟶
          limit (quotientCohomologySystem f I F p))
      (h : ι ≫ π = 0),
      (ShortComplex.mk ι π h).ShortExact)

/- Lemma 52.7.3 (2): under the same Noetherian, coherence, and finite-cohomology
hypotheses, if `f` is proper then the first derived limit of the positive
quotient cohomology tower vanishes in every degree. -/
@[stacks 0A0M] #check (AlgebraicGeometry.Scheme.ModuleDerived.DerivedCompletion.firstDerivedLimitIsZeroOfProper :
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A]
    {X : Scheme.{u}} [IsNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (I : Ideal A) (F : X.Modules) [F.IsCoherent]
    (hfinite : ∀ q : ℤ,
      Module.Finite A
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) q).obj
          ((Scheme.FlatPullbackSections.baseSections f).obj
            ((ModuleCech.moduleToDerived X).obj F))))
    (p : ℤ),
    IsZero (quotientCohomologySystem f I F (p - 1)).firstDerivedLimit)
