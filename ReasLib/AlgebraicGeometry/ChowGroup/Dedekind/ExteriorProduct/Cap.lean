module

public import ReasLib.AlgebraicGeometry.BivariantClass.Dedekind.Commutation
public import ReasLib.AlgebraicGeometry.Scheme.Over.ProductMap

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Dedekind

namespace Total

/-- The cap action of a degree-`q` bivariant class on total relative Chow homology
is the additive map assembled from its degreewise cap maps in a cartesian square. -/
noncomputable def cap
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {U V : Over S} [LocallyOfFiniteType U.hom] [LocallyOfFiniteType V.hom]
    {f : U ⟶ V} {q : ℤ} (c : BivariantClass δ f q)
    {U' V' : Over S} [LocallyOfFiniteType U'.hom] [LocallyOfFiniteType V'.hom]
    (i : U' ⟶ U) (f' : U' ⟶ V') (k : V' ⟶ V) [LocallyOfFiniteType k.left]
    (square : IsPullback i.left f'.left f.left k.left) :
    Total δ V' →+ Total δ U' :=
  DirectSum.toAddMonoid fun d ↦
    (DirectSum.of _ (d - q)).comp (c.cap i f' k square d)

/-- Total cap sends a homogeneous class of degree `d` to its degreewise cap
in degree `d - q`. -/
theorem cap_of
    {S : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    {U V : Over S} [LocallyOfFiniteType U.hom] [LocallyOfFiniteType V.hom]
    {f : U ⟶ V} {q : ℤ} (c : BivariantClass δ f q)
    {U' V' : Over S} [LocallyOfFiniteType U'.hom] [LocallyOfFiniteType V'.hom]
    (i : U' ⟶ U) (f' : U' ⟶ V') (k : V' ⟶ V) [LocallyOfFiniteType k.left]
    (square : IsPullback i.left f'.left f.left k.left)
    (d : ℤ) (a : RelativeChow δ V' d) :
    cap δ c i f' k square (DirectSum.of _ d a) =
      DirectSum.of _ (d - q) (c.cap i f' k square d a) := sorry

end Total

/-- Over a locally Dedekind base, exterior product by a homogeneous Chow class
commutes with the cap action of a bivariant class after product base change. -/
theorem exteriorProduct_cap_homogeneous
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (g : Y ⟶ Z) (n m q : ℤ)
    (α : RelativeChow δ X n) (c' : BivariantClass δ g q)
    (β : RelativeChow δ Z m) :
    RelativeChow.castDegree δ
        (show n + (m - q) - 1 = (n + m - 1) - q by omega)
        (ExteriorProduct.pairing δ h_delta X Y n (m - q) α
          (c'.cap (𝟙 Y) g (𝟙 Z) IsPullback.of_id_fst m β)) =
      c'.cap (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z)
        (Limits.prod.snd : X ⨯ Z ⟶ Z)
        (Scheme.overProdMapSndIsPullback X g) (n + m - 1)
        (ExteriorProduct.pairing δ h_delta X Z n m α β) := sorry

/-- Over a locally Dedekind base, exterior product by any total Chow class
commutes with the cap action of a bivariant class after product base change. -/
theorem exteriorProduct_cap
    {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (g : Y ⟶ Z) (q : ℤ)
    (α : Total δ X) (c' : BivariantClass δ g q) (β : Total δ Z) :
    Total.exteriorProduct δ h_delta X Y α
        (Total.cap δ c' (𝟙 Y) g (𝟙 Z) IsPullback.of_id_fst β) =
      Total.cap δ c' (Limits.prod.snd : X ⨯ Y ⟶ Y)
        (Limits.prod.map (𝟙 X) g : X ⨯ Y ⟶ X ⨯ Z)
        (Limits.prod.snd : X ⨯ Z ⟶ Z) (Scheme.overProdMapSndIsPullback X g)
        (Total.exteriorProduct δ h_delta X Z α β) := sorry

end AlgebraicGeometry.ChowGroup.Dedekind
