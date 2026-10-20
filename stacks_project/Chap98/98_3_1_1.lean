module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation.Map
import StacksCheckRecall

/-!
# Functoriality of predeformation categories

A 1-morphism of categories fibred in groupoids over a locally Noetherian base induces
a functor of the associated predeformation categories over `ArtinianLocalAlgCat Λ k`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

/- 98.3.1.1: a 1-morphism F : X ⟶ Y of categories fibred in groupoids over Over S
induces a functor map F x0 : F_{X, k, x0} ⥤ᵇ F_{Y, k, y0} of categories over
ArtinianLocalAlgCat Λ k, sending x0 ⟶ x to F(x0) ⟶ F(x), where
y0 is residueImage F x0. -/
@[stacks 07WJ]
#check (AlgebraicGeometry.GroupoidsOver.Predeformation.map :
  ∀ {S : Scheme} [IsLocallyNoetherian S] {Λ k : Type} [CommRing Λ]
    [IsNoetherianRing Λ] [Field k] [Algebra Λ k] [Module.Finite Λ k]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    {kToS : Spec (CommRingCat.of k) ⟶ S} [LocallyOfFiniteType kToS]
    (h_factor : Spec.map (CommRingCat.ofHom (algebraMap Λ k)) ≫ openImmersion = kToS)
    {X Y : FiberedCategoryOver.Groupoids (Over S)} (F : X ⟶ Y)
    (x0 : X.p.Fiber (Over.mk kToS)),
    AlgebraicGeometry.GroupoidsOver.Predeformation.predeformation
        openImmersion h_factor X x0 ⥤ᵇ
      AlgebraicGeometry.GroupoidsOver.Predeformation.predeformation
        openImmersion h_factor Y
          (AlgebraicGeometry.GroupoidsOver.Predeformation.residueImage F x0))
