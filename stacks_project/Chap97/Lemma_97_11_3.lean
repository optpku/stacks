module

public import stacks_project.Chap67.Definition_67_46_2_FiniteLocallyFree
public import stacks_project.Chap94.Definition_94_12_2_Etale
public import stacks_project.Chap97.Lemma_97_11_3_Map

/-!
# Étale and surjective restriction of scalars

If `X' ⟶ X` is étale and `Z ⟶ B` is finite locally free, the induced map
`Res_{Z/B}(X') ⟶ Res_{Z/B}(X)` is representable by algebraic spaces and étale,
and is surjective when `X' ⟶ X` is also surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars

/-- Lemma 97.11.3 (1): let `S` be a scheme and let `X' ⟶ X ⟶ Z ⟶ B` be morphisms
of algebraic spaces over `S`. If `h : X' ⟶ X` is étale and `g : Z ⟶ B` is finite
locally free, then `mapGroupoids h f g : toGroupoids (h ≫ f) g ⟶ toGroupoids f g`
is representable by algebraic spaces and étale. -/
@[stacks 05YD, instance]
instance instEtale_map {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S}
    (h : X' ⟶ X) (f : X ⟶ Z) (g : Z ⟶ B)
    [AlgebraicSpace.Etale h] [FiniteLocallyFree g] :
    Groupoids.Hom.Etale (mapGroupoids h f g) :=
  sorry

/-- Lemma 97.11.3 (2): let `S` be a scheme and let `X' ⟶ X ⟶ Z ⟶ B` be morphisms
of algebraic spaces over `S`. If `h : X' ⟶ X` is étale and surjective and
`g : Z ⟶ B` is finite locally free, then
`mapGroupoids h f g : toGroupoids (h ≫ f) g ⟶ toGroupoids f g` is surjective. -/
@[stacks 05YD, instance]
instance instSurjective_map {S : Scheme.{u}} {X' X Z B : AlgebraicSpace S}
    (h : X' ⟶ X) (f : X ⟶ Z) (g : Z ⟶ B)
    [AlgebraicSpace.Etale h] [AlgebraicSpace.Surjective h] [FiniteLocallyFree g] :
    Groupoids.Hom.Surjective (mapGroupoids h f g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RestrictionOfScalars
