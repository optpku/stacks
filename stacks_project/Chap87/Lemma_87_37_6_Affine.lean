module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.AffinePresentation
public import stacks_project.Chap87.Lemma_87_37_4_Completion

/-!
# Affine formal algebraic spaces, functor of points

The affine presentation API is supplied by its mathematical owner. The legacy
completion interface and directed-colimit name remain available to consumers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.FormalAlgebraicSpace Opposite

universe u v

namespace AlgebraicGeometry.AffineFormalAlgebraicSpace

/-- A directed affine thickening colimit uses affine stages, thickening transitions,
and an fppf-local isomorphism from their Yoneda colimit. -/
abbrev IsDirectedAffineThickeningColimit {S : Scheme.{u}} {Λ : Type v} [Preorder Λ]
    [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S) (X : (Over S)ᵒᵖ ⥤ Type u) : Prop :=
  FormalAlgebraicSpace.IsDirectedAffineThickeningColimit D X

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsAffine :
    ∀ {S : Scheme.{u}}, ((Over S)ᵒᵖ ⥤ Type u) → Prop)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsAffine.of :
    ∀ {S : Scheme.{u}} {X : (Over S)ᵒᵖ ⥤ Type u} {Λ : Type u}
    [Preorder Λ] [IsDirected Λ (· ≤ ·)] (D : Λ ⥤ Over S)
    (hcolim : IsDirectedAffineThickeningColimit D X)
    {U R : Over S} (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU)
    (hπU : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU)
    (hσ : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ),
    IsAffine X)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsAffine.spec :
    ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u) [IsAffine X],
    (∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·)) (D : Λ ⥤ Over S),
      IsDirectedAffineThickeningColimit D X) ∧
      ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X) (σ : yoneda.obj R ⟶ pullback πU πU),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsAffine.iff :
    ∀ {S : Scheme.{u}} (X : (Over S)ᵒᵖ ⥤ Type u),
    IsAffine X ↔
      (∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
          (D : Λ ⥤ Over S),
        IsDirectedAffineThickeningColimit D X) ∧
        ∃ (U R : Over S) (πU : yoneda.obj U ⟶ X)
          (σ : yoneda.obj R ⟶ pullback πU πU),
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) πU ∧
            Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) σ)

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsAffine.instYoneda :
    ∀ {S : Scheme.{u}} (U : Over S)
    [AlgebraicGeometry.IsAffine U.left],
    IsAffine (yoneda.obj U))

#check (AlgebraicGeometry.AffineFormalAlgebraicSpace.IsAffine.instIsFormalAlgebraicSpace :
    ∀ {S : Scheme.{u}}
    (X : (Over S)ᵒᵖ ⥤ Type u) [IsAffine X],
    IsFormalAlgebraicSpace X)

end AlgebraicGeometry.AffineFormalAlgebraicSpace
