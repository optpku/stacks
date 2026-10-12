/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.OpenSubspace
import Mathlib.Tactic.CrossRefAttribute

/-!
# Gluing derived modules over two opens

This leaf owns the restriction coherence used to glue derived modules over a two-open cover.
The opens and ambient target are inferred from the local objects and morphisms whenever their
types determine them.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.TwoOpen

open OpenSubspace.Restriction

variable {X : RingedSpace.{u}}

/-- The canonical comparison between the restrictions through `U` and through `V` of an ambient
derived module, both restricted further to `U ⊓ V`. -/
@[stacks 08DG "canonical overlap comparison for two-open derived gluing"]
abbrev overlapIso (U V : Opens X.carrier) (F : ModuleDerived X) :
    (derivedBetween X inf_le_left).obj ((moduleRestrictionToOpenDerived X U).obj F) ≅
      (derivedBetween X inf_le_right).obj ((moduleRestrictionToOpenDerived X V).obj F) :=
  (derivedCompIso X inf_le_left).app F ≪≫
    ((derivedCompIso X inf_le_right).app F).symm

/-- Two restriction isomorphisms realize an ambient derived module as a gluing of local objects
when their overlap square agrees with the prescribed isomorphism. -/
@[stacks 08DG "two-open derived gluing compatibility"]
abbrev IsGluing {U V : Opens X.carrier}
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    (c : (derivedBetween X inf_le_left).obj A ≅
      (derivedBetween X inf_le_right).obj B)
    {F : ModuleDerived X} (eU : (moduleRestrictionToOpenDerived X U).obj F ≅ A)
    (eV : (moduleRestrictionToOpenDerived X V).obj F ≅ B) : Prop :=
  CommSq (overlapIso U V F).hom
    ((derivedBetween X inf_le_left).map eU.hom)
    ((derivedBetween X inf_le_right).map eV.hom) c.hom

/-- The commutative square carried by a two-open gluing witness. -/
@[stacks 08DG "two-open derived gluing square"]
theorem IsGluing.commSq {U V : Opens X.carrier}
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    {c : (derivedBetween X inf_le_left).obj A ≅
      (derivedBetween X inf_le_right).obj B}
    {F : ModuleDerived X} {eU : (moduleRestrictionToOpenDerived X U).obj F ≅ A}
    {eV : (moduleRestrictionToOpenDerived X V).obj F ≅ B}
    (h : IsGluing c eU eV) :
    CommSq (overlapIso U V F).hom
      ((derivedBetween X inf_le_left).map eU.hom)
      ((derivedBetween X inf_le_right).map eV.hom) c.hom := sorry

/-- Equational form of the overlap square carried by a two-open gluing witness. -/
@[stacks 08DG "two-open derived gluing equation"]
theorem IsGluing.w {U V : Opens X.carrier}
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    {c : (derivedBetween X inf_le_left).obj A ≅
      (derivedBetween X inf_le_right).obj B}
    {F : ModuleDerived X} {eU : (moduleRestrictionToOpenDerived X U).obj F ≅ A}
    {eV : (moduleRestrictionToOpenDerived X V).obj F ≅ B}
    (h : IsGluing c eU eV) :
    (overlapIso U V F).hom ≫ (derivedBetween X inf_le_right).map eV.hom =
      (derivedBetween X inf_le_left).map eU.hom ≫ c.hom := sorry

/-- Local morphisms into an ambient target are compatible when they agree on the overlap after
transport by the prescribed local gluing isomorphism. -/
@[stacks 08DG "compatibility of local morphisms for two-open gluing"]
abbrev Compatible {U V : Opens X.carrier}
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    (c : (derivedBetween X inf_le_left).obj A ≅
      (derivedBetween X inf_le_right).obj B)
    {E : ModuleDerived X} (a : A ⟶ (moduleRestrictionToOpenDerived X U).obj E)
    (b : B ⟶ (moduleRestrictionToOpenDerived X V).obj E) : Prop :=
  CommSq c.hom ((derivedBetween X inf_le_left).map a)
    ((derivedBetween X inf_le_right).map b) (overlapIso U V E).hom

/-- The commutative square carried by compatible local morphisms. -/
@[stacks 08DG "two-open local morphism compatibility square"]
theorem Compatible.commSq {U V : Opens X.carrier}
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    {c : (derivedBetween X inf_le_left).obj A ≅
      (derivedBetween X inf_le_right).obj B}
    {E : ModuleDerived X} {a : A ⟶ (moduleRestrictionToOpenDerived X U).obj E}
    {b : B ⟶ (moduleRestrictionToOpenDerived X V).obj E}
    (h : Compatible c a b) :
    CommSq c.hom ((derivedBetween X inf_le_left).map a)
      ((derivedBetween X inf_le_right).map b) (overlapIso U V E).hom := sorry

/-- Equational form of compatibility of local morphisms on the overlap. -/
@[stacks 08DG "two-open local morphism compatibility equation"]
theorem Compatible.w {U V : Opens X.carrier}
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    {c : (derivedBetween X inf_le_left).obj A ≅
      (derivedBetween X inf_le_right).obj B}
    {E : ModuleDerived X} {a : A ⟶ (moduleRestrictionToOpenDerived X U).obj E}
    {b : B ⟶ (moduleRestrictionToOpenDerived X V).obj E}
    (h : Compatible c a b) :
    c.hom ≫ (derivedBetween X inf_le_right).map b =
      (derivedBetween X inf_le_left).map a ≫ (overlapIso U V E).hom := sorry

/-- Lemma 20.45.1 (1): compatible derived modules on two opens covering a ringed space glue to
an ambient derived module. -/
@[stacks 08DG "two-open derived gluing existence"]
theorem existsObj (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    (A : moduleDerivedOnOpen X U) (B : moduleDerivedOnOpen X V)
    (c : (derivedBetween X inf_le_left).obj A ≅
      (derivedBetween X inf_le_right).obj B) :
    ∃ (F : ModuleDerived X) (eU : (moduleRestrictionToOpenDerived X U).obj F ≅ A)
      (eV : (moduleRestrictionToOpenDerived X V).obj F ≅ B), IsGluing c eU eV := sorry

/-- Lemma 20.45.1 (2): compatible local morphisms out of a fixed two-open gluing extend to an
ambient morphism. -/
@[stacks 08DG "extension of compatible morphisms from a two-open derived gluing"]
theorem existsHom (U V : Opens X.carrier) (hUV : U ⊔ V = ⊤)
    {A : moduleDerivedOnOpen X U} {B : moduleDerivedOnOpen X V}
    {c : (derivedBetween X inf_le_left).obj A ≅
      (derivedBetween X inf_le_right).obj B}
    {F : ModuleDerived X} (eU : (moduleRestrictionToOpenDerived X U).obj F ≅ A)
    (eV : (moduleRestrictionToOpenDerived X V).obj F ≅ B) (hF : IsGluing c eU eV)
    {E : ModuleDerived X} (a : A ⟶ (moduleRestrictionToOpenDerived X U).obj E)
    (b : B ⟶ (moduleRestrictionToOpenDerived X V).obj E) (h : Compatible c a b) :
    ∃ f : F ⟶ E,
      (moduleRestrictionToOpenDerived X U).map f = eU.hom ≫ a ∧
        (moduleRestrictionToOpenDerived X V).map f = eV.hom ≫ b := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived.Gluing.TwoOpen

end
