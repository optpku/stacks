module

public import ReasLib.CategoryTheory.DerivedCategory.Bounded
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.GlobalSections.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Quasicoherent.RightAdjoint

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.Modules CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh

/-- For a quasi-compact and quasi-separated algebraic space, the quasicoherent
coreflection of a derived module has uniformly bounded cohomological amplitude
on complexes whose affine-étale hypercohomology is bounded. -/
theorem rightAdjoint_bounds_of_affineEtaleHypercohomology
    {S : Scheme.{u}} (X : AlgebraicSpace S)
    [IsQuasiCompact X] [IsAbsolutelyQuasiSeparated X] :
    ∃ N : ℤ, ∀ (K : ModuleDerived X) (a b : ℤ),
      (∀ {U : AlgebraicSpace S} (φ : U ⟶ X) [IsAffine U] [Etale φ],
          ∀ i : ℤ, i ∉ Set.Icc a b →
            IsZero (cohomologyAb U ((restrictFunctorDerived φ).obj K) i)) →
        ((inclusion X).rightAdjoint.obj K).obj.IsGE a ∧
          ((inclusion X).rightAdjoint.obj K).obj.IsLE (b + N) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
