module

public import stacks_project.Chap92.Lemma_92_18_7_Functoriality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Biproduct
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Derived.Localization
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
variable [UnivLE.{u, u}]

-- Local instance justification (defeq pin): `moduleCategoryHasDerivedCategory` is the reducible standard owner for ringed-site modules; `DerivedCategory.Q` needs that same instance without registering a second derived-category owner.
attribute [local instance] moduleCategoryHasDerivedCategory

/-- The product homomorphism `A ⟶ B ⨯ B'` induced by a pair of ring-sheaf maps. -/
def prodHom {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    A ⟶ B ⨯ B' :=
  prod.lift φ ψ

/-- Unfolding of `prodHom` as `prod.lift`. -/
theorem prodHom_eq {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodHom φ ψ = prod.lift φ ψ :=
  sorry

/-- First projection of a product of sheaves of rings. -/
def prodFst (B B' : Sheaf J CommRingCat.{u}) : B ⨯ B' ⟶ B :=
  prod.fst

/-- Second projection of a product of sheaves of rings. -/
def prodSnd (B B' : Sheaf J CommRingCat.{u}) : B ⨯ B' ⟶ B' :=
  prod.snd

/-- The product homomorphism projects to the first factor. -/
theorem prodHom_comp_fst {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodHom φ ψ ≫ prodFst B B' = φ :=
  sorry

/-- The product homomorphism projects to the second factor. -/
theorem prodHom_comp_snd {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodHom φ ψ ≫ prodSnd B B' = ψ :=
  sorry

/-- The morphism of `Under A` corresponding to first projection of a product of algebras. -/
def fstHom {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    Under.mk (prodHom φ ψ) ⟶ Under.mk φ :=
  Under.homMk (prodFst B B') (prodHom_comp_fst φ ψ)

/-- The morphism of `Under A` corresponding to second projection of a product of algebras. -/
def sndHom {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    Under.mk (prodHom φ ψ) ⟶ Under.mk ψ :=
  Under.homMk (prodSnd B B') (prodHom_comp_snd φ ψ)

/-- `L(φ)` viewed in cochain complexes of `(B ⨯ B')`-modules by restriction along `prodFst`. -/
abbrev prodRestrictLeft {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    CochainComplex (SheafOfModules (ringSheaf J (B ⨯ B'))) ℤ :=
  ((restrictionAlong (prodFst B B')).mapHomologicalComplex (up ℤ)).obj L(φ)

/-- Unfolding of `prodRestrictLeft` as restriction of scalars along `prodFst`. -/
theorem prodRestrictLeft_eq {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) :
    prodRestrictLeft φ =
      ((restrictionAlong (prodFst B B')).mapHomologicalComplex (up ℤ)).obj L(φ) :=
  sorry

/-- `L(ψ)` viewed in cochain complexes of `(B ⨯ B')`-modules by restriction along `prodSnd`. -/
abbrev prodRestrictRight {A B B' : Sheaf J CommRingCat.{u}} (ψ : A ⟶ B') :
    CochainComplex (SheafOfModules (ringSheaf J (B ⨯ B'))) ℤ :=
  ((restrictionAlong (prodSnd B B')).mapHomologicalComplex (up ℤ)).obj L(ψ)

/-- Unfolding of `prodRestrictRight` as restriction of scalars along `prodSnd`. -/
theorem prodRestrictRight_eq {A B B' : Sheaf J CommRingCat.{u}} (ψ : A ⟶ B') :
    prodRestrictRight ψ =
      ((restrictionAlong (prodSnd B B')).mapHomologicalComplex (up ℤ)).obj L(ψ) :=
  sorry

/-- Functoriality map of cotangent complexes after extending scalars along `prodFst`. -/
def prodMapLeftExtend {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    ((extendAlong (prodFst B B')).mapHomologicalComplex (up ℤ)).obj L(prodHom φ ψ) ⟶
      L(φ) :=
  map (fstHom φ ψ)

/-- Unfolding of `prodMapLeftExtend` as `map` along `fstHom`. -/
theorem prodMapLeftExtend_eq {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodMapLeftExtend φ ψ = map (fstHom φ ψ) :=
  sorry

/-- Functoriality map of cotangent complexes after extending scalars along `prodSnd`. -/
def prodMapRightExtend {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    ((extendAlong (prodSnd B B')).mapHomologicalComplex (up ℤ)).obj L(prodHom φ ψ) ⟶
      L(ψ) :=
  map (sndHom φ ψ)

/-- Unfolding of `prodMapRightExtend` as `map` along `sndHom`. -/
theorem prodMapRightExtend_eq {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodMapRightExtend φ ψ = map (sndHom φ ψ) :=
  sorry

/-- Left component of the product comparison, as the adjunct of `prodMapLeftExtend`. -/
def prodMapLeftCochain {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    L(prodHom φ ψ) ⟶ prodRestrictLeft φ :=
  (Adjunction.mapHomologicalComplexAdjunction (extendRestrictAdj (prodFst B B'))
      (up ℤ)).homEquiv L(prodHom φ ψ) L(φ) (prodMapLeftExtend φ ψ)

/-- Right component of the product comparison, as the adjunct of `prodMapRightExtend`. -/
def prodMapRightCochain {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    L(prodHom φ ψ) ⟶ prodRestrictRight ψ :=
  (Adjunction.mapHomologicalComplexAdjunction (extendRestrictAdj (prodSnd B B'))
      (up ℤ)).homEquiv L(prodHom φ ψ) L(ψ) (prodMapRightExtend φ ψ)

/-- Canonical cochain-level product comparison
`L(B ⨯ B' / A) ⟶ L(B/A) ⊕ L(B'/A)` over `B ⨯ B'`. -/
def prodMapCochain {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    L(prodHom φ ψ) ⟶ prodRestrictLeft φ ⊞ prodRestrictRight ψ :=
  biprod.lift (prodMapLeftCochain φ ψ) (prodMapRightCochain φ ψ)

/-- Unfolding of `prodMapCochain` as `biprod.lift` of the two adjuncts. -/
theorem prodMapCochain_eq {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodMapCochain φ ψ = biprod.lift (prodMapLeftCochain φ ψ) (prodMapRightCochain φ ψ) :=
  sorry

/-- The first projection recovers the left adjunct. -/
theorem prodMapCochain_fst {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodMapCochain φ ψ ≫ biprod.fst = prodMapLeftCochain φ ψ :=
  sorry

/-- The second projection recovers the right adjunct. -/
theorem prodMapCochain_snd {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodMapCochain φ ψ ≫ biprod.snd = prodMapRightCochain φ ψ :=
  sorry

/-- Canonical derived product comparison
`L(B ⨯ B' / A) ⟶ L(B/A) ⊕ L(B'/A)` in `D(B ⨯ B')`. -/
def prodMap {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    DerivedCategory.Q.obj L(prodHom φ ψ) ⟶
      DerivedCategory.Q.obj (prodRestrictLeft φ ⊞ prodRestrictRight ψ) :=
  DerivedCategory.Q.map (prodMapCochain φ ψ)

/-- Unfolding of `prodMap` as `DerivedCategory.Q.map` of `prodMapCochain`. -/
theorem prodMap_eq {A B B' : Sheaf J CommRingCat.{u}} (φ : A ⟶ B) (ψ : A ⟶ B') :
    prodMap φ ψ = DerivedCategory.Q.map (prodMapCochain φ ψ) :=
  sorry

end SheafOfModules.RingedSite.CotangentComplex
