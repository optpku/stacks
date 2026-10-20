module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.ChosenFppf.Representable
import StacksCheckRecall

/-!
# Lemma 87.11.3

A morphism from an algebraic space over `S` to a formal algebraic space over
`S` is representable by algebraic spaces.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology
open AlgebraicGeometry AlgebraicGeometry.ChosenBigFppfSite

noncomputable section

universe u v

/- Lemma 87.11.3: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism from an
algebraic space over `S` to a formal algebraic space over `S`. Then `f` is
representable by algebraic spaces. -/
@[stacks 0AIQ] #check
  (AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces.of_isAlgebraicSpace :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y),
    representableByAlgebraicSpaces f)

#check
  (AlgebraicGeometry.ChosenBigFppfSite.instIsAlgebraicSpace_pullback_hom :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    [IsAlgebraicSpace X] [IsFormalAlgebraicSpace Y] (f : X ⟶ Y)
    {U : 𝒮.bigSite S} (ξ : (𝒮.bigTopology S).sheafifiedRepresentable U ⟶ Y),
    IsAlgebraicSpace (pullback ξ f))
