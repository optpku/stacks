module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Cech.Koszul.Hom
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.9.2: the colimit of the contragredient Hom complexes of the powered Koszul
complexes is canonically isomorphic to the alternating Cech complex, functorially in the
coefficient module. -/
@[stacks 08D0] #check
  (LocalizedModule.Away.Cech.Koszul.homColimitIso :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A) (M : ModuleCat A),
      CategoryTheory.Limits.colimit (LocalizedModule.Away.Cech.Koszul.homSystem f M) ≅
        LocalizedModule.Away.Cech.Alternating.complex f M)

/- The canonical comparison commutes with postcomposition along every coefficient-module
morphism. -/
#check
  (LocalizedModule.Away.Cech.Koszul.homColimitIso_hom_naturality :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
      {M N : ModuleCat A} (g : M ⟶ N),
      CategoryTheory.Limits.colim.map
          (LocalizedModule.Away.Cech.Koszul.homSystemMap f g) ≫
          (LocalizedModule.Away.Cech.Koszul.homColimitIso f N).hom =
        (LocalizedModule.Away.Cech.Koszul.homColimitIso f M).hom ≫
          (LocalizedModule.Away.Cech.Alternating.Tensor.complexIso f M).hom ≫
          (CategoryTheory.NatTrans.mapHomologicalComplex
            ((MonoidalCategory.curriedTensor (ModuleCat A)).map g)
              (ComplexShape.up ℕ)).app
                (LocalizedModule.Away.Cech.Alternating.complex f A) ≫
          (LocalizedModule.Away.Cech.Alternating.Tensor.complexIso f N).inv)

end
