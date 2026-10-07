module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import stacks_project.Chap87.Definition_87_11_1_Representable
public import stacks_project.Chap87.Definition_87_9_1_Affine

/-!
# Formal algebraic spaces

A sheaf on a chosen big fppf site `(Sch/S)_fppf` is a formal algebraic space when
it admits an étale jointly surjective atlas by affine formal algebraic spaces,
with each chart representable by algebraic spaces, and it satisfies the
coequalizer size condition on that same site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry

/-- A sheaf on `(Sch/S)_fppf` is a formal algebraic space when it admits an
étale jointly surjective atlas by affine formal algebraic spaces, each chart
representable by algebraic spaces, and it satisfies the coequalizer size
condition. -/
class IsFormalAlgebraicSpace {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) : Prop
    extends IsCoequalizerOfRepresentables X where
  /-- There is an étale jointly surjective atlas by affine formal algebraic
  spaces whose charts are representable by algebraic spaces. -/
  exists_atlas :
    ∃ (ι : Type (max u v))
      (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
        (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
          (∀ i, etale (π i)) ∧
            Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π)

namespace IsFormalAlgebraicSpace

/-- An affine formal algebraic space is a formal algebraic space. -/
instance ofAffine {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] : IsFormalAlgebraicSpace X := sorry

/-- A sheaf is a formal algebraic space iff it satisfies the coequalizer size
condition and admits an étale jointly surjective affine atlas. -/
theorem iff {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v))) :
    IsFormalAlgebraicSpace X ↔
      IsCoequalizerOfRepresentables X ∧
        ∃ (ι : Type (max u v))
          (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
          (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
            (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
              (∀ i, etale (π i)) ∧
                Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) := sorry

/-- A formal algebraic space unpacks as an étale jointly surjective affine
atlas, with charts representable by algebraic spaces, together with the
coequalizer size condition. -/
theorem spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsFormalAlgebraicSpace X] :
    ∃ (ι : Type (max u v))
      (X_ : ι → Sheaf (𝒮.bigTopology S) (Type (max u v)))
      (π : ∀ i, X_ i ⟶ X) (c : Cofan X_) (hc : IsColimit c),
        (∀ i, IsAffineFormalAlgebraicSpace (X_ i)) ∧
          (∀ i, representableByAlgebraicSpaces (π i)) ∧
            (∀ i ⦃U : 𝒮.bigSite S⦄
              (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X),
                ChosenBigFppfSite.IsEtale (pullback.fst ξ (π i))) ∧
              Sheaf.IsLocallySurjective (Cofan.IsColimit.desc hc π) ∧
                IsCoequalizerOfRepresentables X := sorry

end IsFormalAlgebraicSpace

end AlgebraicGeometry
