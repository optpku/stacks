module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import ReasLib.CategoryTheory.Sites.LocallyConstant.Morphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w

namespace CategoryTheory.Sheaf

section Types

variable (X : Scheme.{u})
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (Type w)]
variable {F G : Sheaf X.smallEtaleTopology (Type w)} (φ : F ⟶ G)
variable [IsFiniteLocallyConstant F] [IsLocallyConstant G]

/- Lemma 59.64.5 (1): for a morphism of locally constant sheaves of sets with finite
source, an étale cover makes the morphism one between constant sheaves. -/
@[stacks 095C] #check (CategoryTheory.Sheaf.IsFiniteLocallyConstant.hom_hasConstantChartCover φ :
  ∃ (I : Type (u + 1)) (U : I → X.Etale), X.smallEtaleTopology.CoversTop U ∧
    ∀ i : I,
      ∃ (A B : Type w) (f : A ⟶ B)
          (eF : F.over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i)) (Type w)).obj A)
          (eG : G.over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i)) (Type w)).obj B),
        Finite A ∧
          CommSq ((X.smallEtaleTopology.overPullback (Type w) (U i)).map φ)
            eF.hom eG.hom
            ((constantSheaf (X.smallEtaleTopology.over (U i)) (Type w)).map f))

end Types

section AddCommGroups

variable (X : Scheme.{u})
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) AddCommGrpCat.{w}]
variable {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}} (φ : F ⟶ G)
variable [IsFiniteLocallyConstantAddCommGrp F] [IsLocallyConstant G]

/- Lemma 59.64.5 (2): for a morphism of locally constant sheaves of abelian groups with
finite source, an étale cover makes the morphism one between constant abelian sheaves. -/
@[stacks 095C] #check (CategoryTheory.Sheaf.IsFiniteLocallyConstantAddCommGrp.hom_hasConstantChartCover φ :
  ∃ (I : Type (u + 1)) (U : I → X.Etale), X.smallEtaleTopology.CoversTop U ∧
    ∀ i : I,
      ∃ (A B : AddCommGrpCat.{w}) (f : A ⟶ B)
          (eF : F.over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i)) AddCommGrpCat.{w}).obj A)
          (eG : G.over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i)) AddCommGrpCat.{w}).obj B),
        Finite A ∧
          CommSq ((X.smallEtaleTopology.overPullback AddCommGrpCat.{w} (U i)).map φ)
            eF.hom eG.hom
            ((constantSheaf (X.smallEtaleTopology.over (U i)) AddCommGrpCat.{w}).map f))

end AddCommGroups

section Modules

variable (X : Scheme.{u})
variable {Λ : Type w} [Ring Λ]
variable [∀ U : X.Etale,
  HasWeakSheafify (X.smallEtaleTopology.over U) (ModuleCat.{w} Λ)]
variable {F G : Sheaf X.smallEtaleTopology (ModuleCat.{w} Λ)} (φ : F ⟶ G)
variable [IsFiniteTypeLocallyConstantModule F] [IsLocallyConstant G]

/- Lemma 59.64.5 (3): for a morphism of locally constant sheaves of `Λ`-modules with
finite-type source, an étale cover makes the morphism one between constant `Λ`-module sheaves. -/
@[stacks 095C] #check (CategoryTheory.Sheaf.IsFiniteTypeLocallyConstantModule.hom_hasConstantChartCover φ :
  ∃ (I : Type (u + 1)) (U : I → X.Etale), X.smallEtaleTopology.CoversTop U ∧
    ∀ i : I,
      ∃ (M N : ModuleCat.{w} Λ) (f : M ⟶ N)
          (eF : F.over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i)) (ModuleCat.{w} Λ)).obj M)
          (eG : G.over (U i) ≅
            (constantSheaf (X.smallEtaleTopology.over (U i)) (ModuleCat.{w} Λ)).obj N),
        Module.Finite Λ M ∧
          CommSq ((X.smallEtaleTopology.overPullback (ModuleCat.{w} Λ) (U i)).map φ)
            eF.hom eG.hom
            ((constantSheaf (X.smallEtaleTopology.over (U i))
              (ModuleCat.{w} Λ)).map f))

end Modules

end CategoryTheory.Sheaf
