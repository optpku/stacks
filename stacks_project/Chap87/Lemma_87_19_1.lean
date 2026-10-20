module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ChosenFppf.Composition
import StacksCheckRecall

@[expose] public section

universe u v

open CategoryTheory AlgebraicGeometry Limits ChosenBigFppfSite

namespace AlgebraicGeometry.ChosenBigFppfSite

/- Lemma 87.19.1: The composition of morphisms representable by algebraic
spaces is representable by algebraic spaces. The same holds for morphisms
representable by schemes. -/
@[stacks 0APY] #check
  (AlgebraicGeometry.ChosenBigFppfSite.representableByAlgebraicSpaces.comp :
    ∀ {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]
    [HasPullbacks (Sheaf (𝒮.bigTopology S) (Type (max u v)))]
    {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : representableByAlgebraicSpaces f) (hg : representableByAlgebraicSpaces g),
    representableByAlgebraicSpaces (f ≫ g))

section

variable {𝒮 : ChosenBigFppfSite.{u, v}} {S : 𝒮.carrier}
    [HasWeakSheafify (𝒮.bigTopology S) (Type (max u v))]

#check (CategoryTheory.MorphismProperty.comp_mem
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable :
    ∀ {X Y Z : Sheaf (𝒮.bigTopology S) (Type (max u v))}
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable f)
    (hg : (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable g),
    (𝒮.bigTopology S).sheafifiedRepresentableFunctor.relativelyRepresentable (f ≫ g))

end

end AlgebraicGeometry.ChosenBigFppfSite
