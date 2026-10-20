/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Abelian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FibrePower.OffDiagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.GlobalSections
public import ReasLib.RepresentationTheory.PermutationSign

/-! # Permutation actions on off-diagonal sections -/

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Identification `(ρ σ)^* (F|_W) ≅ F|_W` coming from the permutation lying over `X`. -/
noncomputable def offDiagonalRestrictionPastingIso {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Separated f] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1} ⋙
        etaleRestrictionSheaf (offDiagonalPerm f n σ).hom AddCommGrpCat.{u + 1} ≅
      etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1} :=
  Functor.sheafPushforwardContinuousComp'
    (eqToIso ((etaleRestriction_comp (offDiagonalPerm f n σ).hom
        (offDiagonalToBase f n)).symm.trans
      (by
        have restriction_congr :
            ∀ (a b : offDiagonal f n ⟶ X) (ha : Etale a) (hb : Etale b),
              a = b → @etaleRestriction S _ _ a ha = @etaleRestriction S _ _ b hb := by
          intro a b ha hb hab
          cases hab
          rfl
        exact restriction_congr _ _ inferInstance inferInstance
          (offDiagonalPerm_comp_toBase f n σ))))
    AddCommGrpCat.{u + 1} (smallEtaleTopology (offDiagonal f n))
    (smallEtaleTopology (offDiagonal f n)) (smallEtaleTopology X)

/-- The lifted symmetric-group action on off-diagonal sections by inverse pullback. -/
noncomputable def offDiagonalSectionsAction {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    (F : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}) :
    ULift.{u} (Equiv.Perm (Fin n)) →* Aut
      ((globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F)) where
  toFun σ :=
    { hom :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (offDiagonalPerm f n σ.down⁻¹).hom ≫
                (etaleRestrictionSheaf (offDiagonalPerm f n σ.down⁻¹).hom
                    AddCommGrpCat.{u + 1}).map s ≫
                  (offDiagonalRestrictionPastingIso f n σ.down⁻¹).hom.app F
            map_zero' := sorry
            map_add' := sorry }
      inv :=
        AddCommGrpCat.ofHom
          { toFun := fun s =>
              constantIntegerPullbackHom (offDiagonalPerm f n σ.down).hom ≫
                (etaleRestrictionSheaf (offDiagonalPerm f n σ.down).hom
                    AddCommGrpCat.{u + 1}).map s ≫
                  (offDiagonalRestrictionPastingIso f n σ.down).hom.app F
            map_zero' := sorry
            map_add' := sorry }
      hom_inv_id := sorry
      inv_hom_id := sorry }
  map_one' := sorry
  map_mul' := sorry

/-- The map on `F(W)` induced by a morphism of abelian sheaves on `X_étale`. -/
noncomputable def offDiagonalSectionsMap {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    (globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj F) ⟶
      (globalSections (offDiagonal f n)).obj
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).obj G) :=
  (globalSections (offDiagonal f n)).map
    ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).map φ)

/-- `offDiagonalSectionsMap` is global sections of étale restriction of `φ`. -/
theorem offDiagonalSectionsMap_eq {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    offDiagonalSectionsMap f n φ =
      (globalSections (offDiagonal f n)).map
        ((etaleRestrictionSheaf (offDiagonalToBase f n) AddCommGrpCat.{u + 1}).map φ) :=
  rfl

/-- Restriction of abelian sheaves is equivariant for the off-diagonal permutation
action on global sections. -/
theorem offDiagonalSectionsMap_equivariant {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    ∀ g : ULift.{u} (Equiv.Perm (Fin n)),
      (offDiagonalSectionsAction f n F g).hom ≫ offDiagonalSectionsMap f n φ =
        offDiagonalSectionsMap f n φ ≫ (offDiagonalSectionsAction f n G g).hom :=
  sorry

/-- The map on `S_n`-anti-invariants of `F(W)` induced by a morphism of abelian
sheaves. -/
noncomputable def offDiagonalAntiInvariantsMap {U X : AlgebraicSpace S}
    (f : U ⟶ X) [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    IntegerCharacter.invariants (offDiagonalSectionsAction f n F) (IntegerCharacter.permutationSign n) ⟶
      IntegerCharacter.invariants (offDiagonalSectionsAction f n G) (IntegerCharacter.permutationSign n) :=
  IntegerCharacter.map (IntegerCharacter.permutationSign n) (offDiagonalSectionsMap f n φ)
    (offDiagonalSectionsMap_equivariant f n φ)

/-- `offDiagonalAntiInvariantsMap` is the equivariant `IntegerCharacter.map` of
`offDiagonalSectionsMap`. -/
theorem offDiagonalAntiInvariantsMap_eq {U X : AlgebraicSpace S} (f : U ⟶ X)
    [Etale f] [Separated f] (n : ℕ)
    {F G : Sheaf (smallEtaleTopology X) AddCommGrpCat.{u + 1}} (φ : F ⟶ G) :
    offDiagonalAntiInvariantsMap f n φ =
      IntegerCharacter.map (IntegerCharacter.permutationSign n) (offDiagonalSectionsMap f n φ)
        (offDiagonalSectionsMap_equivariant f n φ) :=
  rfl

end AlgebraicGeometry.AlgebraicSpace
