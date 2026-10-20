/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.Span
public import ReasLib.Algebra.Category.Ring.Sheaf.LocallyRinged
import Mathlib.Tactic.CrossRefAttribute

/-!
# Sectionwise criteria for local unit dichotomy

The reusable datum is the binary factorization morphism of underlying type-valued sheaves.  Its
local surjectivity and the finite unit-ideal cover condition are equivalent views of local unit
dichotomy.
-/

@[expose] public section

open CategoryTheory Limits Opposite

noncomputable section

universe u v

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget CommRingCat.{max u v})]
variable [HasWeakSheafify J (Type (max u v))]

/-- Type-valued sheaves on a site have the canonical binary coproducts inherited from
type-valued presheaves. -/
instance hasBinaryCoproducts :
    HasColimitsOfShape (Discrete WalkingPair) (Sheaf J (Type (max u v))) :=
  Sheaf.instHasColimitsOfShape

/-- The second coordinate `(f, a) ↦ a * f` of the left binary-factorization branch. -/
def binaryFactorizationLeftSecond (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (𝒪.underlyingType ⨯ 𝒪.underlyingType) ⟶
      𝒪.underlyingType where
  hom :=
    { app := fun U ↦ TypeCat.ofHom fun x ↦
        (fun a f : 𝒪.obj.obj U ↦ a * f)
          ((prod.snd : 𝒪.underlyingType ⨯ 𝒪.underlyingType ⟶
            𝒪.underlyingType).hom.app U x)
          ((prod.fst : 𝒪.underlyingType ⨯ 𝒪.underlyingType ⟶
            𝒪.underlyingType).hom.app U x)
      naturality := sorry }

/-- The left branch `(f, a) ↦ (f, a * f)` of the binary factorization morphism. -/
def binaryFactorizationLeft (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (𝒪.underlyingType ⨯ 𝒪.underlyingType) ⟶
      𝒪.underlyingType ⨯ 𝒪.underlyingType :=
  prod.lift prod.fst (binaryFactorizationLeftSecond 𝒪)

/-- The second coordinate `(f, b) ↦ b * (1 - f)` of the right binary-factorization branch. -/
def binaryFactorizationRightSecond (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (𝒪.underlyingType ⨯ 𝒪.underlyingType) ⟶
      𝒪.underlyingType where
  hom :=
    { app := fun U ↦ TypeCat.ofHom fun x ↦
        (fun b f : 𝒪.obj.obj U ↦ b * (1 - f))
          ((prod.snd : 𝒪.underlyingType ⨯ 𝒪.underlyingType ⟶
            𝒪.underlyingType).hom.app U x)
          ((prod.fst : 𝒪.underlyingType ⨯ 𝒪.underlyingType ⟶
            𝒪.underlyingType).hom.app U x)
      naturality := sorry }

/-- The right branch `(f, b) ↦ (f, b * (1 - f))` of the binary factorization morphism. -/
def binaryFactorizationRight (𝒪 : Sheaf J CommRingCat.{max u v}) :
    (𝒪.underlyingType ⨯ 𝒪.underlyingType) ⟶
      𝒪.underlyingType ⨯ 𝒪.underlyingType :=
  prod.lift prod.fst (binaryFactorizationRightSecond 𝒪)

/-- The binary factorization morphism whose two branches express factorization through `f` and
through `1 - f`. -/
def binaryFactorizationMap (𝒪 : Sheaf J CommRingCat.{max u v}) :
    ((𝒪.underlyingType ⨯ 𝒪.underlyingType) ⨿
        (𝒪.underlyingType ⨯ 𝒪.underlyingType)) ⟶
      𝒪.underlyingType ⨯ 𝒪.underlyingType :=
  coprod.desc (binaryFactorizationLeft 𝒪) (binaryFactorizationRight 𝒪)

/-- Every finite nonempty family of sections generating the unit ideal locally contains a unit. -/
def FiniteUnitIdealCover (𝒪 : Sheaf J CommRingCat.{max u v}) : Prop :=
  ∀ (U : C) (s : Set (𝒪.obj.obj (op U))), s.Finite → s.Nonempty → Ideal.span s = ⊤ →
    ∃ S : J.Cover U, ∀ I : S.Arrow,
      ∃ g ∈ s, IsUnit ((𝒪.obj.map I.f.op).hom g)

omit [J.HasSheafCompose (forget CommRingCat.{max u v})]
  [HasWeakSheafify J (Type (max u v))] in
/-- Local unit dichotomy is equivalent to the finite unit-ideal cover condition. -/
theorem localUnitDichotomy_iff_finiteUnitIdealCover
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    𝒪.LocalUnitDichotomy ↔ FiniteUnitIdealCover 𝒪 := sorry

/-- Local unit dichotomy is equivalent to local surjectivity of the binary factorization map. -/
theorem localUnitDichotomy_iff_binaryFactorizationMap_locallySurjective
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    𝒪.LocalUnitDichotomy ↔ IsLocallySurjective (binaryFactorizationMap 𝒪) := sorry

/-- The finite unit-ideal cover condition is equivalent to local surjectivity of the binary
factorization map. -/
theorem finiteUnitIdealCover_iff_binaryFactorizationMap_locallySurjective
    (𝒪 : Sheaf J CommRingCat.{max u v}) :
    FiniteUnitIdealCover 𝒪 ↔ IsLocallySurjective (binaryFactorizationMap 𝒪) := sorry

/-- Lemma 18.40.1 (04ES): local unit dichotomy, the finite unit-ideal cover condition, and local
surjectivity of the binary factorization map are equivalent. -/
@[stacks 04ES]
theorem localUnit_tfae (𝒪 : Sheaf J CommRingCat.{max u v}) :
    List.TFAE [
      𝒪.LocalUnitDichotomy,
      FiniteUnitIdealCover 𝒪,
      IsLocallySurjective (binaryFactorizationMap 𝒪)
    ] := sorry

-- The objectwise branch maps are explicit; `sorryAx` is confined to their naturality laws.

end CategoryTheory.Sheaf
