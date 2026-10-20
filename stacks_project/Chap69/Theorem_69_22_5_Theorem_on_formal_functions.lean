module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Cohomology.FormalFunctions
import StacksCheckRecall

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules
open CategoryTheory CategoryTheory.Limits

universe u

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `higherDirectImage` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `cohomologyOver`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

/- Theorem 69.22.5 (Theorem on formal functions)
The canonical comparison from completed cohomology to the inverse limit of
ideal-power quotient cohomology is an isomorphism in every degree. -/
@[stacks 08AZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.isIso_limitComparison :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [IsNoetherianRing A] (I : Ideal A)
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
      (F : X.Modules) [F.IsCoherent]
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules] (p : ℕ),
      IsIso (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.limitComparison I f F p))

/- The same canonical comparison is a homeomorphism for the limit topologies. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.isHomeomorph_limitComparison :
    ∀ {A : Type u} [CommRing A]
      {X : AlgebraicSpace (Spec (CommRingCat.of A))}
      [IsNoetherianRing A] (I : Ideal A)
      (f : X ⟶ ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))) [Proper f]
      (F : X.Modules) [F.IsCoherent]
      [Abelian X.Modules]
      [Abelian (ofOver (Over.mk (𝟙 (Spec (CommRingCat.of A))))).Modules]
      [HasInjectiveResolutions X.Modules] (p : ℕ),
      @IsHomeomorph
        (AdicCompletion I
          (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p))
        (limit (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.quotientSystem I f F p) : ModuleCat A)
        (⨅ n, TopologicalSpace.induced
          (AdicCompletion.eval I
            (GradedCohomology.cohomologyOver (𝟙 (Spec (CommRingCat.of A))) f F p) n) ⊥)
        (Functor.limitTopology (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.quotientSystem I f F p))
        (AlgebraicGeometry.AlgebraicSpace.Modules.IdealPowerCohomology.limitComparison I f F p).hom)
