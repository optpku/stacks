/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DeRham.Map
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DeRham
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.SheafificationBaseChange
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of ringed-site de Rham complexes

A commutative square of commutative ring sheaves induces a morphism from the
source de Rham complex to the scalar restriction of the target complex.  The
degreewise construction sheafifies the presheaf map and uses the canonical
comparisons between sheafification and restriction of scalars.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace SheafOfModules.RingedSite.DeRham

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{max u v})]
variable [HasWeakSheafify J AddCommGrpCat.{max u v}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
variable {O₁ O₂ O₁' O₂' : Sheaf J CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {φ : O₁ ⟶ O₂} {φ' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}

/-- Forgetting sheaf conditions turns a commutative square of ring sheaves
into a commutative square of their underlying presheaves. -/
@[stacks 0FKQ "underlying presheaf square for ringed-site de Rham maps"]
theorem square_hom (sq : CommSq a φ φ' b) :
    CommSq a.hom φ.hom φ'.hom b.hom := sorry

/-- The degree-`p` map obtained by sheafifying the objectwise map associated
to a commutative square of ring sheaves. -/
@[stacks 0FKQ "degreewise maps of ringed-site de Rham complexes"]
noncomputable def mapApp (sq : CommSq a φ φ' b) (p : ℕ) :
    term φ p ⟶ (restriction a).obj (term φ' p) :=
  (ModuleSheafification.restrictionComponentIso φ
      (PresheafOfModules.DeRham.form φ.hom p)).inv ≫
    (moduleSheafification O₁).map
      (PresheafOfModules.DeRham.mapApp (square_hom sq) p) ≫
    (ModuleSheafification.restrictionComponentIso a
      (PresheafOfModules.DeRham.term φ'.hom p)).hom ≫
    (restriction a).map
      (ModuleSheafification.restrictionComponentIso φ'
        (PresheafOfModules.DeRham.form φ'.hom p)).hom

/-- Restriction of cochain complexes of module sheaves along the upper
horizontal map. -/
@[stacks 0FKQ "restriction for ringed-site de Rham complexes"]
abbrev complexRestriction (a : O₁ ⟶ O₁') :=
  (restriction a).mapHomologicalComplex (up ℕ)

/-- The sheafified degreewise square maps commute with every de Rham differential. -/
@[stacks 0FKQ "differential compatibility of ringed-site de Rham maps"]
theorem mapApp_comm (sq : CommSq a φ φ' b) (i j : ℕ)
    (hij : (up ℕ).Rel i j) :
    mapApp sq i ≫ ((complexRestriction a).obj (complex φ')).d i j =
      (complex φ).d i j ≫ mapApp sq j := sorry

/-- A commutative square of commutative ring sheaves induces a morphism of
relative de Rham complexes. -/
@[stacks 0FKQ "functoriality of ringed-site de Rham complexes"]
noncomputable def map (sq : CommSq a φ φ' b) :
    complex φ ⟶ (complexRestriction a).obj (complex φ') where
  f p := mapApp sq p
  comm' i j hij := mapApp_comm sq i j hij

/-- The degree-`p` component of the induced sheaf de Rham complex map is the
degreewise sheafified map. -/
@[simp, stacks 0FKQ "degreewise component of ringed-site de Rham maps"]
theorem map_f (sq : CommSq a φ φ' b) (p : ℕ) :
    (map sq).f p = mapApp sq p := sorry

/-- The identity square on a morphism of commutative ring sheaves. -/
@[stacks 0FKQ "identity square for ringed-site de Rham maps"]
theorem idSquare (φ : O₁ ⟶ O₂) :
    CommSq (𝟙 O₁) φ φ (𝟙 O₂) := sorry

namespace Restriction

/-- The canonical comparison from the identity functor to restriction along an identity
commutative-ring-sheaf morphism. -/
@[stacks 0FKQ "identity restriction for ringed-site de Rham maps"]
noncomputable def idIso (O : Sheaf J CommRingCat.{max u v}) :
    (𝟭 (ringedSiteModuleCategory J O) :
        ringedSiteModuleCategory J O ⥤ ringedSiteModuleCategory J O) ≅
      restriction (𝟙 O) :=
  SheafOfModules.Restriction.idIso'
    (ringSheafMap (𝟙 O))
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map_id O)

/-- The canonical comparison from two successive square restrictions to restriction along
their composite. -/
@[stacks 0FKQ "composition restriction for ringed-site de Rham maps"]
noncomputable def compIso
    {O₁'' : Sheaf J CommRingCat.{max u v}}
    (a : O₁ ⟶ O₁') (a' : O₁' ⟶ O₁'') :
    restriction a' ⋙ restriction a ≅ restriction (a ≫ a') :=
  SheafOfModules.Restriction.compIso'
    (ringSheafMap a) (ringSheafMap a') (ringSheafMap (a ≫ a'))
    ((sheafCompose J (forget₂ CommRingCat RingCat)).map_comp a a')

namespace Complex

/-- The complex-level comparison from the identity functor to restriction along an identity
commutative-ring-sheaf morphism. -/
@[stacks 0FKQ "identity restriction for ringed-site de Rham complexes"]
noncomputable def idIso
    (O : Sheaf J CommRingCat.{max u v}) :
    (𝟭 (CochainComplex (ringedSiteModuleCategory J O) ℕ)) ≅
      complexRestriction (𝟙 O) :=
  (Functor.mapHomologicalComplexIdIso
      (ringedSiteModuleCategory J O) (up ℕ)).symm ≪≫
    NatIso.mapHomologicalComplex (Restriction.idIso O) (up ℕ)

/-- The complex-level comparison from two successive square restrictions to restriction along
their composite. -/
@[stacks 0FKQ "composition restriction for ringed-site de Rham complexes"]
noncomputable def compIso
    {O₁'' : Sheaf J CommRingCat.{max u v}}
    (a : O₁ ⟶ O₁') (a' : O₁' ⟶ O₁'') :
    complexRestriction a' ⋙ complexRestriction a ≅
      complexRestriction (a ≫ a') :=
  Functor.mapHomologicalComplexCompIso (Restriction.compIso a a') (up ℕ)

end Complex

end Restriction

/-- The degreewise de Rham map of an identity ring-sheaf square is the canonical
identity-restriction comparison. -/
@[simp, stacks 0FKQ "identity law for ringed-site de Rham maps"]
theorem mapApp_id (φ : O₁ ⟶ O₂) (p : ℕ) :
    mapApp (idSquare φ) p =
      (Restriction.idIso O₁).hom.app (term φ p) := sorry

/-- The de Rham complex map of an identity ring-sheaf square is the canonical
identity-restriction comparison. -/
@[simp, stacks 0FKQ "identity law for ringed-site de Rham complex maps"]
theorem map_id (φ : O₁ ⟶ O₂) :
    map (idSquare φ) =
      (Restriction.Complex.idIso O₁).hom.app (complex φ) := sorry

/-- Degreewise ringed-site de Rham maps preserve horizontal composition after the canonical
comparison of successive scalar restrictions. -/
@[stacks 0FKQ "composition law for degreewise ringed-site de Rham maps"]
theorem mapApp_comp
    {O₁'' O₂'' : Sheaf J CommRingCat.{max u v}}
    {a' : O₁' ⟶ O₁''} {φ'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq : CommSq a φ φ' b) (sq' : CommSq a' φ' φ'' b') (p : ℕ) :
    mapApp sq p ≫ (restriction a).map (mapApp sq' p) ≫
        (Restriction.compIso a a').hom.app (term φ'' p) =
      mapApp (CommSq.horiz_comp sq sq') p := sorry

/-- Ringed-site de Rham complex maps preserve horizontal composition after the canonical
comparison of successive scalar restrictions. -/
@[stacks 0FKQ "composition law for ringed-site de Rham complex maps"]
theorem map_comp
    {O₁'' O₂'' : Sheaf J CommRingCat.{max u v}}
    {a' : O₁' ⟶ O₁''} {φ'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq : CommSq a φ φ' b) (sq' : CommSq a' φ' φ'' b') :
    map sq ≫ (complexRestriction a).map (map sq') ≫
        (Restriction.Complex.compIso a a').hom.app (complex φ'') =
      map (CommSq.horiz_comp sq sq') := sorry

end SheafOfModules.RingedSite.DeRham
