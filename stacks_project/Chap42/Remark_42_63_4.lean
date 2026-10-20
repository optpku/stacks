module

public import ReasLib.AlgebraicGeometry.ChowGroup.Dedekind.ExteriorProduct.Cap
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

open AlgebraicGeometry AlgebraicGeometry.ChowGroup.Dedekind

/- Remark 42.63.4: over a locally Dedekind base, exterior product by any total Chow
class commutes with the cap action of a bivariant class. -/
@[stacks 0FC7]
#check (AlgebraicGeometry.ChowGroup.Dedekind.exteriorProduct_cap :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (g : Y ⟶ Z) (q : ℤ)
    (α : Total δ X) (c' : BivariantClass δ g q) (β : Total δ Z),
    Total.exteriorProduct δ h_delta X Y α
        (Total.cap δ c' (𝟙 Y) g (𝟙 Z) IsPullback.of_id_fst β) =
      Total.cap δ c' (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z)
        (Limits.prod.snd : X ⨯ Z ⟶ Z)
        (Scheme.overProdMapSndIsPullback X g)
        (Total.exteriorProduct δ h_delta X Z α β))
