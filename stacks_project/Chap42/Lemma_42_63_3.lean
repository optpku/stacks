module

public import ReasLib.AlgebraicGeometry.BivariantClass.Dedekind.Commutation
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set

noncomputable section

universe u

namespace AlgebraicGeometry.BivariantClass.Dedekind

/- Lemma 42.63.3: over a locally Dedekind base, after base change to `X ⨯ Z`,
every degree-`p` bivariant class on `X ⟶ S` commutes with every degree-`q`
bivariant class on `Y ⟶ Z`; the canonical common pullback is identified with
`X ⨯ Y`. -/
@[stacks 0FC6] #check (AlgebraicGeometry.BivariantClass.Dedekind.commute :
  ∀ {S : Scheme.{u}} [UniversallyCatenary S]
    [S.HasRingPropertyLocally (fun A : CommRingCat.{u} ↦ IsDedekindDomain A)]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h_delta : ∀ s : S,
      δ s = @ite ℤ (IsClosed ({s} : Set S)) (Classical.propDecidable _) 0 1)
    {X Y Z : Over S} [LocallyOfFiniteType X.hom]
    [LocallyOfFiniteType Y.hom] [LocallyOfFiniteType Z.hom]
    (g : Y ⟶ Z) (p q : ℤ)
    (c : BivariantClass δ (baseMap X) p)
    (c' : BivariantClass δ g q),
    Commute δ (Limits.prod.snd : X ⨯ Z ⟶ Z) g
      (restrict δ (Limits.prod.fst : X ⨯ Z ⟶ X)
        (Limits.prod.snd : X ⨯ Z ⟶ Z) (baseMap Z)
        (productIsPullback X (baseMap Z)) p c) c')

end AlgebraicGeometry.BivariantClass.Dedekind
