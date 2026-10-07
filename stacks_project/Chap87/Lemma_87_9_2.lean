module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_9_1_Affine

/-!
# Lemma 87.9.2

The diagonal of an affine formal algebraic space is representable and a closed
immersion in the sense of a representable transformation of fppf sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- Lemma 87.9.2 (1): Let `S` be a scheme. If `X` is an affine formal algebraic
space over `S`, then the diagonal morphism `Δ : X ⟶ X ×_S X` is representable. -/
@[stacks 0AI8]
theorem relativelyRepresentable_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) :=
  sorry

/-- Lemma 87.9.2 (2): Let `S` be a scheme. If `X` is an affine formal algebraic
space over `S`, then the diagonal morphism `Δ : X ⟶ X ×_S X` is a closed
immersion. -/
@[stacks 0AI8]
theorem isClosedImmersion_diag {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    (MorphismProperty.inverseImage (@IsClosedImmersion) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor (diag X) :=
  sorry

/-- Relative closed-immersion of the diagonal unpacks as relative representability
together with closed immersions of represented pullbacks on source schemes. -/
theorem isClosedImmersion_diag_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    (X : Sheaf (𝒮.bigTopology S) (Type (max u v)))
    [IsAffineFormalAlgebraicSpace X] :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (diag X) ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ X ⨯ X)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) (diag X) ξ →
          IsClosedImmersion ((𝒮.bigToScheme S).map snd) :=
  sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
