module

public import ReasLib.Algebra.Category.Ring.Sheaf
public import Mathlib.CategoryTheory.Limits.Types.Coproducts
public import Mathlib.CategoryTheory.Limits.Types.Products
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Locally ringed sheaves on a site

This file owns the site-theoretic notion of a locally ringed commutative-ring sheaf.  The
definition is independent of any presentation of a ringed topos and keeps the two mathematical
conditions separate: local unit dichotomy and local nontriviality.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v w

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Every local section is locally either a unit or has unit complement. -/
@[stacks 04ES "local unit dichotomy"]
class LocalUnitDichotomy (𝒪 : Sheaf J CommRingCat.{w}) : Prop where
  local_unit_dichotomy (U : C) (f : 𝒪.obj.obj (op U)) :
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      IsUnit ((𝒪.obj.map I.f.op).hom f) ∨
        IsUnit (1 - (𝒪.obj.map I.f.op).hom f)

section LocallyRinged

variable [HasWeakSheafify J (Type (max u v))]
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]

/-- The underlying type-valued sheaf of a commutative-ring sheaf. -/
abbrev underlyingType (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf J (Type (max u v)) :=
  (sheafCompose J (forget CommRingCat.{max u v})).obj 𝒪

/-- The zero section of the underlying type-valued sheaf of a commutative-ring sheaf. -/
def zeroSection (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf.terminal J Types.isTerminalPUnit ⟶ underlyingType 𝒪 where
  hom :=
    { app := fun U ↦ TypeCat.ofHom fun _ ↦ (0 : 𝒪.obj.obj U)
      naturality := sorry }

/-- The unit section of the underlying type-valued sheaf of a commutative-ring sheaf. -/
def oneSection (𝒪 : Sheaf J CommRingCat.{max u v}) :
    Sheaf.terminal J Types.isTerminalPUnit ⟶ underlyingType 𝒪 where
  hom :=
    { app := fun U ↦ TypeCat.ofHom fun _ ↦ (1 : 𝒪.obj.obj U)
      naturality := sorry }

/-- The canonical map from the sheafification of the empty presheaf to the equalizer of the
zero and unit sections.  It presents the local nontriviality condition without choosing points
or stalks. -/
@[stacks 04EU "local nontriviality map", stacks 05D7]
def nontrivialityMap (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (presheafToSheaf J (Type (max u v))).obj (⊥_ (Cᵒᵖ ⥤ Type (max u v))) ⟶
      equalizer (zeroSection 𝒪) (oneSection 𝒪) :=
  (((sheafificationAdjunction J (Type (max u v))).homEquiv
      (⊥_ (Cᵒᵖ ⥤ Type (max u v)))
      (equalizer (zeroSection 𝒪) (oneSection 𝒪))).symm <|
    initial.to ((sheafToPresheaf J (Type (max u v))).obj
      (equalizer (zeroSection 𝒪) (oneSection 𝒪))))

/-- A commutative-ring sheaf on a site is locally ringed when it is locally nontrivial and every
section is locally either a unit or has unit complement. -/
@[stacks 04EU, stacks 04H8]
class IsLocallyRinged (𝒪 : Sheaf J CommRingCat.{max u v}) : Prop
    extends IsIso (nontrivialityMap 𝒪), LocalUnitDichotomy 𝒪

/-- The two defining conditions assemble into the canonical locally ringed-sheaf instance. -/
instance isLocallyRinged_of_conditions
    (𝒪 : Sheaf J CommRingCat.{max u v})
    [IsIso (nontrivialityMap 𝒪)] [LocalUnitDichotomy 𝒪] :
    IsLocallyRinged 𝒪 :=
  { toIsIso := inferInstance
    toLocalUnitDichotomy := inferInstance }

end LocallyRinged

end CategoryTheory.Sheaf
