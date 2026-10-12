/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Presheaf.DeRham
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Restriction
public import ReasLib.RingTheory.Kaehler.DeRham.Map
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Functoriality of presheaf de Rham complexes

A commutative square of commutative-ring presheaves induces a morphism from
the source de Rham complex to the scalar restriction of the target complex.
The construction is objectwise the corresponding algebraic map.
-/

@[expose] public section

open CategoryTheory ComplexShape

noncomputable section

universe u v

namespace PresheafOfModules.DeRham

variable {C : Type u} [Category.{v} C]
variable {O₁ O₂ O₁' O₂' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
variable {a : O₁ ⟶ O₁'} {φ : O₁ ⟶ O₂} {φ' : O₁' ⟶ O₂'} {b : O₂ ⟶ O₂'}

/-- Evaluation turns a commutative square of ring presheaves into a
commutative square of section rings. -/
@[stacks 0FKQ "sectionwise square for presheaf de Rham maps"]
theorem square_app (sq : CommSq a φ φ' b) (X : Cᵒᵖ) :
    CommSq (a.app X) (φ.app X) (φ'.app X) (b.app X) := sorry

/-- The objectwise degree-`p` map induced by a commutative square of ring
presheaves. -/
@[stacks 0FKQ "maps of presheaf de Rham complexes"]
noncomputable def mapComponent (sq : CommSq a φ φ' b) (p : ℕ) (X : Cᵒᵖ) :
    (term φ p).obj X ⟶ ((restriction a).obj (term φ' p)).obj X :=
  CommRingCat.DeRham.mapApp (square_app sq X) p

/-- The objectwise maps induced by a ring-presheaf square commute with restriction maps. -/
@[stacks 0FKQ "naturality of presheaf de Rham map components"]
theorem mapComponent_naturality (sq : CommSq a φ φ' b) (p : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (term φ p).map f ≫
        (ModuleCat.restrictScalars (((ringPresheaf O₁).map f).hom)).map
          (mapComponent sq p Y) =
      mapComponent sq p X ≫ ((restriction a).obj (term φ' p)).map f := sorry

/-- The degree-`p` morphism of module presheaves induced by a commutative
square of commutative-ring presheaves. -/
@[stacks 0FKQ "degreewise maps of presheaf de Rham complexes"]
noncomputable def mapApp (sq : CommSq a φ φ' b) (p : ℕ) :
    term φ p ⟶ (restriction a).obj (term φ' p) where
  app X := mapComponent sq p X
  naturality f := mapComponent_naturality sq p f

/-- Evaluation of the degreewise presheaf de Rham map recovers its objectwise component. -/
@[simp, stacks 0FKQ "evaluation of degreewise presheaf de Rham maps"]
theorem mapApp_app (sq : CommSq a φ φ' b) (p : ℕ) (X : Cᵒᵖ) :
    (mapApp sq p).app X = mapComponent sq p X := sorry

/-- Restriction of cochain complexes of module presheaves along the upper
horizontal map. -/
@[stacks 0FKQ "restriction for presheaf de Rham complexes"]
abbrev complexRestriction (a : O₁ ⟶ O₁') :=
  (restriction a).mapHomologicalComplex (up ℕ)

/-- The degreewise square maps commute with every differential of the de Rham complex. -/
@[stacks 0FKQ "differential compatibility of presheaf de Rham maps"]
theorem mapApp_comm (sq : CommSq a φ φ' b) (i j : ℕ)
    (hij : (up ℕ).Rel i j) :
    mapApp sq i ≫ ((complexRestriction a).obj (complex φ')).d i j =
      (complex φ).d i j ≫ mapApp sq j := sorry

/-- A commutative square of commutative-ring presheaves induces a morphism of
relative de Rham complexes. -/
@[stacks 0FKQ "functoriality of presheaf de Rham complexes"]
noncomputable def map (sq : CommSq a φ φ' b) :
    complex φ ⟶ (complexRestriction a).obj (complex φ') where
  f p := mapApp sq p
  comm' i j hij := mapApp_comm sq i j hij

/-- The degree-`p` component of the induced de Rham complex map is the
degreewise square map. -/
@[simp, stacks 0FKQ "degreewise component of presheaf de Rham maps"]
theorem map_f (sq : CommSq a φ φ' b) (p : ℕ) :
    (map sq).f p = mapApp sq p := sorry

/-- The identity square on a morphism of commutative-ring presheaves. -/
@[stacks 0FKQ "identity square for presheaf de Rham maps"]
theorem idSquare (φ : O₁ ⟶ O₂) :
    CommSq (𝟙 O₁) φ φ (𝟙 O₂) := sorry

namespace Restriction

/-- The canonical comparison from the identity functor to restriction along an identity
commutative-ring-presheaf morphism. -/
@[stacks 0FKQ "identity restriction for presheaf de Rham maps"]
noncomputable def idIso (O : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    (𝟭 (PresheafOfModules (ringPresheaf O)) :
        PresheafOfModules (ringPresheaf O) ⥤
          PresheafOfModules (ringPresheaf O)) ≅
      restriction (𝟙 O) :=
  PresheafOfModules.Restriction.idIso (ringPresheaf O)

/-- The canonical comparison from two successive square restrictions to restriction along
their composite. -/
@[stacks 0FKQ "composition restriction for presheaf de Rham maps"]
noncomputable def compIso
    {O₁'' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    (a : O₁ ⟶ O₁') (a' : O₁' ⟶ O₁'') :
    restriction a' ⋙ restriction a ≅ restriction (a ≫ a') :=
  PresheafOfModules.Restriction.compIso
    (presheafStructureMap a) (presheafStructureMap a')

namespace Complex

/-- The complex-level comparison from the identity functor to restriction along an identity
commutative-ring-presheaf morphism. -/
@[stacks 0FKQ "identity restriction for presheaf de Rham complexes"]
noncomputable def idIso
    (O : Cᵒᵖ ⥤ CommRingCat.{max u v}) :
    (𝟭 (CochainComplex (PresheafOfModules (ringPresheaf O)) ℕ)) ≅
      complexRestriction (𝟙 O) :=
  (Functor.mapHomologicalComplexIdIso
      (PresheafOfModules (ringPresheaf O)) (up ℕ)).symm ≪≫
    NatIso.mapHomologicalComplex (Restriction.idIso O) (up ℕ)

/-- The complex-level comparison from two successive square restrictions to restriction along
their composite. -/
@[stacks 0FKQ "composition restriction for presheaf de Rham complexes"]
noncomputable def compIso
    {O₁'' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    (a : O₁ ⟶ O₁') (a' : O₁' ⟶ O₁'') :
    complexRestriction a' ⋙ complexRestriction a ≅
      complexRestriction (a ≫ a') :=
  Functor.mapHomologicalComplexCompIso (Restriction.compIso a a') (up ℕ)

end Complex

end Restriction

/-- The degreewise de Rham map of an identity presheaf square is the canonical
identity-restriction comparison. -/
@[simp, stacks 0FKQ "identity law for presheaf de Rham maps"]
theorem mapApp_id (φ : O₁ ⟶ O₂) (p : ℕ) :
    mapApp (idSquare φ) p =
      (Restriction.idIso O₁).hom.app (term φ p) := sorry

/-- The de Rham complex map of an identity presheaf square is the canonical
identity-restriction comparison. -/
@[simp, stacks 0FKQ "identity law for presheaf de Rham complex maps"]
theorem map_id (φ : O₁ ⟶ O₂) :
    map (idSquare φ) =
      (Restriction.Complex.idIso O₁).hom.app (complex φ) := sorry

/-- Degreewise presheaf de Rham maps preserve horizontal composition after the canonical
comparison of successive scalar restrictions. -/
@[stacks 0FKQ "composition law for degreewise presheaf de Rham maps"]
theorem mapApp_comp
    {O₁'' O₂'' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {a' : O₁' ⟶ O₁''} {φ'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq : CommSq a φ φ' b) (sq' : CommSq a' φ' φ'' b') (p : ℕ) :
    mapApp sq p ≫ (restriction a).map (mapApp sq' p) ≫
        (Restriction.compIso a a').hom.app (term φ'' p) =
      mapApp (CommSq.horiz_comp sq sq') p := sorry

/-- Presheaf de Rham complex maps preserve horizontal composition after the canonical
comparison of successive scalar restrictions. -/
@[stacks 0FKQ "composition law for presheaf de Rham complex maps"]
theorem map_comp
    {O₁'' O₂'' : Cᵒᵖ ⥤ CommRingCat.{max u v}}
    {a' : O₁' ⟶ O₁''} {φ'' : O₁'' ⟶ O₂''} {b' : O₂' ⟶ O₂''}
    (sq : CommSq a φ φ' b) (sq' : CommSq a' φ' φ'' b') :
    map sq ≫ (complexRestriction a).map (map sq') ≫
        (Restriction.Complex.compIso a a').hom.app (complex φ'') =
      map (CommSq.horiz_comp sq sq') := sorry

end PresheafOfModules.DeRham
