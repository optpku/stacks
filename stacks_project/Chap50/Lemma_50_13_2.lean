module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.LerayHirsch.Absolute
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSite.Hom
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham.LerayHirsch

/- Lemma 50.13.2: for a smooth proper triangle `X ⟶ Y ⟶ S` with `Y` and `S`
affine, finitely many homogeneous classes in `H_dR(X/S)` whose restrictions form a basis on
every residue-field fiber induce, in every degree, the isomorphism
`(a i) ↦ ∑ i, ξ i ∪ f⁺(a i)` of `Γ(S, 𝒪_S)`-modules from shifted copies of
`H_dR(Y/S)` to `H_dR(X/S)`. -/
@[stacks 0FUM] #check
  (AlgebraicGeometry.Scheme.DeRham.LerayHirsch.cohomologyMap_isIso :
    ∀ {X Y S : Scheme.{u}} (f : X ⟶ Y) (a : X ⟶ S) (b : Y ⟶ S)
      (sq : CommSq f a b (𝟙 S))
      [Smooth f] [IsProper f] [IsAffine Y] [IsAffine S]
      [Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived.{u} (Cohomology.coefficientHom sq))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite a.toLRSHom.toShHom))]
      [∀ y : Y, Functor.HasRightDerivedFunctor
        (modulePushforwardToDerived.{u} (Cohomology.coefficientHom (fiberSquare sq y)))
        (ModuleQis.{u} (RingedSpace.DeRham.coefficientSite
          (f.fiberToSpecResidueField y).toLRSHom.toShHom))]
      [MonoidalCategory (coefficientDerived a)]
      [(DerivedCategory.Qh :
        HomotopyCategory (coefficientModules a) (ComplexShape.up ℤ) ⥤
          coefficientDerived a).Monoidal]
      [CoefficientGlobalLaxMonoidal a]
      {N : ℕ} (n : Fin N → ℕ) (ξ : ∀ i, cohomology a (n i : ℤ))
      (hξ : IsAbsoluteFiberwiseBasis sq n ξ),
      ∀ q : ℤ, IsIso (cohomologyMap sq n ξ q))

end AlgebraicGeometry.Scheme.DeRham.LerayHirsch
