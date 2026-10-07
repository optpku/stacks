module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ProperHenselian

open CategoryTheory Opposite
open CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

/- Lemma 59.91.2: if `(A, I)` is a henselian pair and `f : X ⟶ Spec A` is proper,
then restriction to the closed special fibre induces a bijection on étale global
sections for every sheaf of sets on `X`. -/
@[stacks 0A0C] #check
  (AlgebraicGeometry.Scheme.Hom.etaleGlobalSectionsBijectiveOfProperHenselianPair :
    {A : Type u} → [CommRing A] → (I : Ideal A) → [HenselianRing A I] →
      {X : Scheme.{u}} → (f : X ⟶ Spec (CommRingCat.of A)) → [IsProper f] →
      let φ := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
      let i := pullback.fst f φ
      ∀ [HasWeakSheafify X.smallEtaleTopology (Type u)]
        [HasWeakSheafify (pullback f φ).smallEtaleTopology (Type u)]
        [∀ P : X.Etaleᵒᵖ ⥤ Type u,
          (smallEtalePullback i).op.HasLeftKanExtension P]
        (F : Sheaf X.smallEtaleTopology (Type u)),
        Function.Bijective (etaleGlobalSectionsPullback i F))
