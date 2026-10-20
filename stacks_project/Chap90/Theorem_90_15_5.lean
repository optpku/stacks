module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Existence
import StacksCheckRecall

open CategoryTheory ArtinianLocalAlgCat

universe u

/- Theorem 90.15.5. A predeformation category with a minimal versal formal object
having bijective differential satisfies (S1), (S2), and finite-dimensionality of
its canonical tangent space. These conditions imply existence of a minimal
versal formal object with orbit-bijective differential. Under separability of
the residue field over the residue image, the differential conditions coincide. -/
@[stacks 06IX] #check (CategoryTheory.Functor.miniversalExistence :
  ∀ {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] {F : Type (u + 1)} [Category.{u + 1} F]
    (p : F ⥤ ArtinianLocalAlgCat Λ k) [Functor.IsPredeformationCategory p],
    ((∃ ξ : FormalObject p, FormalObject.IsMinimalVersal ξ ∧
        FormalObject.BijectiveDifferential ξ) →
      Functor.HasSchlessingerS1 p ∧ Functor.HasSchlessingerS2 p ∧
        (∀ [Functor.HasSchlessingerS2 p],
          FiniteDimensional k ((Functor.fiberIsoClassFunctor p).obj (dualNumber Λ k)))) ∧
    (∀ [Functor.HasSchlessingerS1 p] [Functor.HasSchlessingerS2 p]
        [FiniteDimensional k ((Functor.fiberIsoClassFunctor p).obj (dualNumber Λ k))],
      ∃ ξ : FormalObject p, FormalObject.IsMinimalVersal ξ ∧
        FormalObject.BijectiveDifferentialOnOrbits ξ) ∧
    (∀ [Algebra.IsSeparable (Algebra.residueImage Λ k) k] (ξ : FormalObject p),
      FormalObject.BijectiveDifferential ξ ↔
        FormalObject.BijectiveDifferentialOnOrbits ξ))
