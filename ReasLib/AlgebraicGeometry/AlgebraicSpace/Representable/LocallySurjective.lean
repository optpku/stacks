module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Surjectivity of flat, locally of finite presentation morphisms of sheaves

A morphism of fppf sheaves on schemes over `S` that is representable by
algebraic spaces and whose base changes along Yoneda sections are flat,
locally of finite presentation, and surjective is locally surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of fppf sheaves of sets on `Over S` that is representable by
algebraic spaces and whose base changes along Yoneda sections are flat, locally
of finite presentation, and surjective is locally surjective for the fppf
topology. -/
theorem isLocallySurjective_of_flat_locallyOfFinitePresentation_surjective
    {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (hF : Presheaf.IsSheaf (Scheme.fppfTopology.over S) F)
    (hG : Presheaf.IsSheaf (Scheme.fppfTopology.over S) G)
    (ha : representableByAlgebraicSpaces a)
    (h_flat : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), Flat (ha.pullbackHom ξ))
    (h_locallyOfFinitePresentation : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G),
      LocallyOfFinitePresentation (ha.pullbackHom ξ))
    (h_surjective :
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), Surjective (ha.pullbackHom ξ)) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) a :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
