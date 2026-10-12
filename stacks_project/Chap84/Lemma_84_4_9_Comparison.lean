/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import ReasLib.CategoryTheory.Abelian.Injective.RightDerived.Composition
public import stacks_project.Chap69.Lemma_69_6_3_DerivedSections
public import stacks_project.Chap69.Lemma_69_6_5_Sections

/-!
# Abelian étale cohomology of algebraic spaces and restriction

Cohomology of an abelian sheaf on the small étale site of an algebraic space is
the right-derived functor of `Hom(ℤ̲, -)`. Restriction along a morphism of
algebraic spaces induces a comparison on global sections and on cohomology.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

-- Local instance justification (defeq pin): `HasInjectiveResolutions` and `Functor.rightDerived` pin the Abelian-induced `Preadditive`/`HasZeroMorphisms` instances for defeq of `etaleCohomologyRestrict`.
attribute [local instance 2000] Abelian.toPreadditive Preadditive.preadditiveHasZeroMorphisms

variable {S : Scheme.{u}}

/-- Étale cohomology of an abelian sheaf on the small étale site of an algebraic
space, as the degree-`q` right-derived functor of `Hom(ℤ̲, -)`. -/
abbrev etaleCohomology (X : AlgebraicSpace S)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ) :
    AddCommGrpCat.{u + 1} :=
  ((globalSections X).rightDerived q).obj F

/-- Evaluating étale cohomology recovers the right-derived global-sections functor. -/
theorem etaleCohomology_eq (X : AlgebraicSpace S)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ) :
    etaleCohomology X F q = ((globalSections X).rightDerived q).obj F :=
  sorry

/-- Identification `Hom(ℤ̲_X, f_* G) ≅ Hom(ℤ̲_Y, G)` via the inverse-image
adjunction and the constant-integer comparison. -/
def homConstantPushforwardIso {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (globalSections X).obj ((sheafPushforwardAbelian f).obj G) ≅
      (globalSections Y).obj G where
  hom :=
    AddCommGrpCat.ofHom
      { toFun := fun φ ↦
          inv (CharacterSections.inverseImageConstantHom f) ≫
            ((sheafInverseImageAdjunction f).homEquiv (constantIntegerSheaf X) G).symm φ
        map_zero' := sorry
        map_add' := sorry }
  inv :=
    AddCommGrpCat.ofHom
      { toFun := fun ψ ↦
          ((sheafInverseImageAdjunction f).homEquiv (constantIntegerSheaf X) G)
            (CharacterSections.inverseImageConstantHom f ≫ ψ)
        map_zero' := sorry
        map_add' := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/-- The forward map of `homConstantPushforwardIso` is adjunction-hom-equivalence
of the inverse constant-integer comparison. -/
theorem homConstantPushforwardIso_hom {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    (G : Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1}) :
    (homConstantPushforwardIso f G).hom =
      AddCommGrpCat.ofHom
        { toFun := fun φ ↦
            inv (CharacterSections.inverseImageConstantHom f) ≫
              ((sheafInverseImageAdjunction f).homEquiv (constantIntegerSheaf X) G).symm φ
          map_zero' := sorry
          map_add' := sorry } :=
  sorry

/-- Natural comparison of abelian global sections
`Γ(X_étale, F) ⟶ Γ(Y_étale, f⁻¹ F)` via the adjunction unit and the
constant-integer identification `Hom(ℤ̲_X, f_* G) ≅ Hom(ℤ̲_Y, G)`. -/
def etaleAbelianSectionsRestrict {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})] :
    globalSections X ⟶
      sheafInverseImage AddCommGrpCat.{u + 1} f ⋙ globalSections Y where
  app F :=
    (globalSections X).map ((sheafInverseImageAdjunction f).unit.app F) ≫
      (homConstantPushforwardIso f
        ((sheafInverseImage AddCommGrpCat.{u + 1} f).obj F)).hom
  naturality _ _ _ := sorry

/-- Evaluating `etaleAbelianSectionsRestrict` recovers postcomposition with the
adjunction unit followed by the constant-integer Hom identification. -/
theorem etaleAbelianSectionsRestrict_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Preadditive (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Preadditive (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    (etaleAbelianSectionsRestrict f).app F =
      (globalSections X).map ((sheafInverseImageAdjunction f).unit.app F) ≫
        (homConstantPushforwardIso f
          ((sheafInverseImage AddCommGrpCat.{u + 1} f).obj F)).hom :=
  sorry

/-- Canonical comparison morphism `H^q(X, F) ⟶ H^q(Y, f⁻¹ F)` on abelian étale
cohomology of algebraic spaces. -/
def etaleCohomologyRestrict {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).Additive]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).PreservesHomology]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).PreservesInjectiveObjects]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f ⋙ globalSections Y).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ) :
    etaleCohomology X F q ⟶
      etaleCohomology Y ((sheafInverseImage AddCommGrpCat.{u + 1} f).obj F) q :=
  (NatTrans.rightDerived (etaleAbelianSectionsRestrict f) q).app F ≫
    (Functor.RightDerived.precompObjIso
        (sheafInverseImage AddCommGrpCat.{u + 1} f) (globalSections Y) q F).hom

/-- Evaluating `etaleCohomologyRestrict` recovers the derived adjunction-unit
comparison followed by the precomposition identification of derived sections. -/
theorem etaleCohomologyRestrict_eq {X Y : AlgebraicSpace S} (f : Y ⟶ X)
    [Abelian (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1})]
    [Abelian (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [HasInjectiveResolutions (Sheaf (smallEtaleTopology Y) AddCommGrpCat.{u + 1})]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).Additive]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).PreservesHomology]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f).PreservesInjectiveObjects]
    [(sheafInverseImage AddCommGrpCat.{u + 1} f ⋙ globalSections Y).Additive]
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) (q : ℕ) :
    etaleCohomologyRestrict f F q =
      (NatTrans.rightDerived (etaleAbelianSectionsRestrict f) q).app F ≫
        (Functor.RightDerived.precompObjIso
            (sheafInverseImage AddCommGrpCat.{u + 1} f) (globalSections Y) q F).hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
