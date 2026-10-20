module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.TwoFibreProduct

open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.GroupoidsOver.Predeformation
open scoped Bicategory

universe u

/- Lemma 98.3.3: A two-fibre product of categories fibred in groupoids induces a
fibre product of their predeformation categories at the images of a residue object. -/
@[stacks 07WL] #check (AlgebraicGeometry.GroupoidsOver.Predeformation.mapCone_isBilimit :
  ∀ {S : Scheme.{u}} [IsLocallyNoetherian S]
    {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (kToS : Spec (CommRingCat.of k) ⟶ S) [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    {W X Y Z : GroupoidsOver S} (fX : X ⟶ Y) (gZ : Z ⟶ Y) (fW : W ⟶ X) (gW : W ⟶ Z)
    (sq : fW ≫ fX ≅ gW ≫ gZ) (w0 : W.p.Fiber (Over.mk kToS))
    [hW : Bicategory.PseudoPullbackCone.IsBilimit
      (⟨W, fW, gW, sq⟩ : Bicategory.PseudoPullbackCone fX gZ)],
    (mapCone openImmersion kToS h_factor fX gZ fW gW sq w0).IsBilimit)
