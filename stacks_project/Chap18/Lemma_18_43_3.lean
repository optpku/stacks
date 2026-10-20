module

public import ReasLib.CategoryTheory.Sites.LocallyConstant.Morphism
import StacksCheckRecall

/-!
# Lemma 18.43.3

Compatibility facade for constant-chart covers of morphisms between locally constant sheaves.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Types

variable [∀ U : C, HasWeakSheafify (J.over U) (Type w)]
variable {F G : Sheaf J (Type w)} (φ : F ⟶ G)
variable [IsFiniteLocallyConstant F] [IsLocallyConstant G]

/- Lemma 18.43.3 (1): locally on a top cover, `φ` is induced by a map from a finite
constant type to a constant type. -/
@[stacks 093S "(1)"]
#check (IsFiniteLocallyConstant.hom_hasConstantChartCover φ :
  ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
    ∀ i : I,
      ∃ (A B : Type w) (f : A ⟶ B)
          (eF : F.over (U i) ≅ (constantSheaf (J.over (U i)) (Type w)).obj A)
          (eG : G.over (U i) ≅ (constantSheaf (J.over (U i)) (Type w)).obj B),
        Finite A ∧ CommSq ((J.overPullback (Type w) (U i)).map φ) eF.hom eG.hom
          ((constantSheaf (J.over (U i)) (Type w)).map f))

end Types

section AddCommGroups

variable [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
variable {F G : Sheaf J AddCommGrpCat.{w}} (φ : F ⟶ G)
variable [IsFiniteLocallyConstantAddCommGrp F] [IsLocallyConstant G]

/- Lemma 18.43.3 (2): locally on a top cover, `φ` is induced by a homomorphism from a finite
constant abelian group to a constant abelian group. -/
@[stacks 093S "(2)"]
#check (IsFiniteLocallyConstantAddCommGrp.hom_hasConstantChartCover φ :
  ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
    ∀ i : I,
      ∃ (A B : AddCommGrpCat.{w}) (f : A ⟶ B)
          (eF : F.over (U i) ≅ (constantSheaf (J.over (U i)) AddCommGrpCat.{w}).obj A)
          (eG : G.over (U i) ≅ (constantSheaf (J.over (U i)) AddCommGrpCat.{w}).obj B),
        Finite A ∧ CommSq ((J.overPullback AddCommGrpCat.{w} (U i)).map φ)
          eF.hom eG.hom ((constantSheaf (J.over (U i)) AddCommGrpCat.{w}).map f))

end AddCommGroups

section Modules

variable {Λ : Type w} [Ring Λ]
variable [∀ U : C, HasWeakSheafify (J.over U) (ModuleCat.{w} Λ)]
variable {F G : Sheaf J (ModuleCat.{w} Λ)} (φ : F ⟶ G)
variable [IsFiniteTypeLocallyConstantModule F] [IsLocallyConstant G]

/- Lemma 18.43.3 (3): locally on a top cover, `φ` is induced by a linear map from a
finite-type constant `Λ`-module to a constant `Λ`-module. -/
@[stacks 093S "(3)"]
#check (IsFiniteTypeLocallyConstantModule.hom_hasConstantChartCover φ :
  ∃ (I : Type (max u v)) (U : I → C), J.CoversTop U ∧
    ∀ i : I,
      ∃ (M N : ModuleCat.{w} Λ) (f : M ⟶ N)
          (eF : F.over (U i) ≅
            (constantSheaf (J.over (U i)) (ModuleCat.{w} Λ)).obj M)
          (eG : G.over (U i) ≅
            (constantSheaf (J.over (U i)) (ModuleCat.{w} Λ)).obj N),
        Module.Finite Λ M ∧
          CommSq ((J.overPullback (ModuleCat.{w} Λ) (U i)).map φ) eF.hom eG.hom
            ((constantSheaf (J.over (U i)) (ModuleCat.{w} Λ)).map f))

end Modules

end CategoryTheory.Sheaf
