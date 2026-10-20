module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.CotangentComplex.Functoriality
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Biproduct
public import ReasLib.CategoryTheory.Adjunction.HomotopyCategory

/-!
# Product comparison of sheaf cotangent complexes

For homomorphisms `A ⟶ B` and `A ⟶ B'` of sheaves of rings, this module owns the canonical
comparison `L(B ⨯ B' / A) ⟶ L(B/A) ⊕ L(B'/A)` in `D(B ⨯ B')`, obtained by adjoining the two
functoriality maps along the product projections and assembling them by `biprod.lift`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open HomologicalComplex
open ComplexShape
open SheafOfModules.RingedSite
open SheafOfModules.RingedSite.CotangentComplex
open scoped SheafOfModules.RingedSite.CotangentComplex

noncomputable section

universe u

namespace SheafOfModules.RingedSite.CotangentComplex

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [J.HasSheafCompose (CategoryTheory.forget CommRingCat.{u})]
variable [HasWeakSheafify J CommRingCat.{u}]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasColimitsOfShape (Discrete WalkingPair) CommRingCat.{u}]

/-- The morphism of `Under A` corresponding to first projection of a product of algebras. -/
def fstHom {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    Under.mk (prod.lift φ ψ) ⟶ Under.mk φ :=
  Under.homMk (prod.fst : B ⨯ B' ⟶ B) (prod.lift_fst φ ψ)

/-- The morphism of `Under A` corresponding to second projection of a product of algebras. -/
def sndHom {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    Under.mk (prod.lift φ ψ) ⟶ Under.mk ψ :=
  Under.homMk (prod.snd : B ⨯ B' ⟶ B') (prod.lift_snd φ ψ)

/-- `L(φ)` viewed in cochain complexes of `(B ⨯ B')`-modules by restriction along the first projection. -/
abbrev prodRestrictLeft {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    CochainComplex (SheafOfModules (ringSheaf J (B ⨯ B'))) ℤ :=
  ((restrictionAlong (prod.fst : B ⨯ B' ⟶ B)).mapHomologicalComplex (up ℤ)).obj L(φ)

/-- `L(ψ)` viewed in cochain complexes of `(B ⨯ B')`-modules by restriction along the second projection. -/
abbrev prodRestrictRight {A B B' : Sheaf J CommRingCat.{u}} (ψ : A ⟶ B') :
    CochainComplex (SheafOfModules (ringSheaf J (B ⨯ B'))) ℤ :=
  ((restrictionAlong (prod.snd : B ⨯ B' ⟶ B')).mapHomologicalComplex (up ℤ)).obj L(ψ)

/-- Left component of the product comparison, as the adjunct of fixed-base functoriality along the first projection. -/
def prodMapLeftCochain {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    L(prod.lift φ ψ) ⟶ prodRestrictLeft φ :=
  (Adjunction.mapHomologicalComplexAdjunction
      (ChangeOfRings.extendRestrictAdjunction (ringSheafMap (prod.fst : B ⨯ B' ⟶ B)))
      (up ℤ)).homEquiv L(prod.lift φ ψ) L(φ) (map (fstHom φ ψ))

/-- Right component of the product comparison, as the adjunct of fixed-base functoriality along the second projection. -/
def prodMapRightCochain {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    L(prod.lift φ ψ) ⟶ prodRestrictRight ψ :=
  (Adjunction.mapHomologicalComplexAdjunction
      (ChangeOfRings.extendRestrictAdjunction (ringSheafMap (prod.snd : B ⨯ B' ⟶ B')))
      (up ℤ)).homEquiv L(prod.lift φ ψ) L(ψ) (map (sndHom φ ψ))

/-- Canonical cochain-level product comparison
`L(B ⨯ B' / A) ⟶ L(B/A) ⊕ L(B'/A)` over `B ⨯ B'`. -/
def prodMapCochain {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    L(prod.lift φ ψ) ⟶ prodRestrictLeft φ ⊞ prodRestrictRight ψ :=
  biprod.lift (prodMapLeftCochain φ ψ) (prodMapRightCochain φ ψ)

/-- The first projection recovers the left adjunct. -/
theorem prodMapCochain_fst {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodMapCochain φ ψ ≫ biprod.fst = prodMapLeftCochain φ ψ :=
  biprod.lift_fst _ _

/-- The second projection recovers the right adjunct. -/
theorem prodMapCochain_snd {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodMapCochain φ ψ ≫ biprod.snd = prodMapRightCochain φ ψ :=
  biprod.lift_snd _ _

/-- Canonical derived product comparison
`L(B ⨯ B' / A) ⟶ L(B/A) ⊕ L(B'/A)` in `D(B ⨯ B')`. -/
def prodMap {A B B' : Sheaf J CommRingCat.{u}}
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (ringSheaf J (B ⨯ B')))]
    (φ : A ⟶ B) (ψ : A ⟶ B') :
    (DerivedCategory.Q.{u + 1}
      (C := SheafOfModules.{u} (ringSheaf J (B ⨯ B')))).obj L(prod.lift φ ψ) ⟶
      (DerivedCategory.Q.{u + 1}
        (C := SheafOfModules.{u} (ringSheaf J (B ⨯ B')))).obj
          (prodRestrictLeft φ ⊞ prodRestrictRight ψ) :=
  (DerivedCategory.Q.{u + 1}
    (C := SheafOfModules.{u} (ringSheaf J (B ⨯ B')))).map (prodMapCochain φ ψ)

/-- The canonical derived comparison from the cotangent complex of a product of ring sheaves
is an isomorphism onto the biproduct of the restricted cotangent complexes of its factors. -/
instance prodMap_isIso {A B B' : Sheaf J CommRingCat.{u}}
    [HasDerivedCategory.{u + 1} (SheafOfModules.{u} (ringSheaf J (B ⨯ B')))]
    (φ : A ⟶ B) (ψ : A ⟶ B') : IsIso (prodMap φ ψ) :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
