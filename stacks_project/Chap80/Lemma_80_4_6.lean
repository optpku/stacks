module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap67.Lemma_67_28_11_LocallyOfFinitePresentation
public import stacks_project.Chap67.Lemma_67_30_5_Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Representable.Pullback

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


/-- Lemma 80.4.6: if `S` is a scheme and `a : F ⟶ G` is a morphism of fppf sheaves
of sets on `Over S` that is representable by algebraic spaces and whose base
changes along Yoneda sections are flat, locally of finite presentation, and
surjective as morphisms of algebraic spaces, then `a` is surjective as a map of
sheaves, in the sense of `Presheaf.IsLocallySurjective` on
`Scheme.fppfTopology.over S`. -/
@[stacks 04S1]
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
