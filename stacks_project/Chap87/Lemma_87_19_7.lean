module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_9_1_Affine
public import stacks_project.Chap87.Definition_87_11_1_Representable

/-!
# Lemma 87.19.7

A morphism of affine formal algebraic spaces that is representable by
algebraic spaces is representable by schemes and affine.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

namespace AlgebraicGeometry
namespace IsAffineFormalAlgebraicSpace

/-- Lemma 87.19.7 (1): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces.
Then `f` is representable by schemes. -/
@[stacks 0AKN]
theorem relativelyRepresentable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f :=
  sorry

/-- Lemma 87.19.7 (2): Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
affine formal algebraic spaces which is representable by algebraic spaces.
Then `f` is affine. -/
@[stacks 0AKN]
theorem isAffineHom_relative {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f) :
    (MorphismProperty.inverseImage (@IsAffineHom) (𝒮.bigToScheme S)).relative
      (𝒮.bigTopology S).sheafifiedRepresentableFunctor f :=
  sorry

/-- Relative affinity of a morphism of affine formal algebraic spaces unpacks as
relative representability together with affinity of represented pullbacks on
source schemes. -/
theorem isAffineHom_relative_spec {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAffineFormalAlgebraicSpace X] [IsAffineFormalAlgebraicSpace Y]
    {f : X ⟶ Y} (hf : representableByAlgebraicSpaces f) :
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f ∧
      ∀ {U V : 𝒮.bigSite S}
        (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y)
        (fst : (𝒮.bigTopology S).sheafifiedRepresentable V ⟶ X) (snd : V ⟶ U),
        IsPullback fst ((𝒮.bigTopology S).sheafifiedRepresentableMap snd) f ξ →
          IsAffineHom ((𝒮.bigToScheme S).map snd) :=
  sorry

end IsAffineFormalAlgebraicSpace
end AlgebraicGeometry
