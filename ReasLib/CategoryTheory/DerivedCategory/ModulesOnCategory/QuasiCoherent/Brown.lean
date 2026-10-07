module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.SmallSources
import Mathlib.Tactic.CrossRefAttribute

/-!
# Brown representability for quasi-coherent derived modules on a chaotic site

This file specializes the universe-sensitive Brown API to the canonical category
`Chaotic.QC 𝒪`.  The structural closure facts remain in `ChaoticClosure`; this leaf owns
representability and right-adjoint consequences.
-/

@[expose] public section

noncomputable section

open CategoryTheory Limits Opposite
open SheafOfModules.RingedSite

universe u v w uD vD

namespace CategoryTheory.ModulesOnCategory.Chaotic

variable {C : Type u} [Category.{v} C]
variable (𝒪 : Sheaf (⊥ : GrothendieckTopology C)
  CommRingCat.{max (max u v) w})
variable [((⊥ : GrothendieckTopology C)).HasSheafCompose
  (forget₂ CommRingCat.{max (max u v) w} RingCat.{max (max u v) w})]

/-- The ambient unbounded derived category of module sheaves on the chaotic ringed site. -/
@[stacks 0GZ0 "ambient derived category"]
abbrev AmbientDerived :=
  DerivedCategory
    (ringedSiteModuleCategory.{u, v, max (max u v) w, max (max u v) w}
      (⊥ : GrothendieckTopology C) 𝒪)

/-- The canonical fully faithful inclusion of quasi-coherent objects into the ambient derived
category. -/
@[stacks 0GZ0 "(1), canonical inclusion"]
abbrev inclusion : QC 𝒪 ⥤ AmbientDerived 𝒪 :=
  ObjectProperty.ι (isQuasiCoherent 𝒪)

/-- Proposition 21.43.9 (0GZ0) (2): every contravariant homological functor on `QC 𝒪`
which sends coproducts indexed in the coefficient universe to products is representable. -/
@[stacks 0GZ0 "(2)"]
theorem existsRepresentation
    (H : (QC 𝒪)ᵒᵖ ⥤
      AddCommGrpCat.{max (max (u + 1) (v + 1)) (w + 1)})
    [H.rightOp.IsHomological]
    [∀ J : Type (max (max u v) w), PreservesLimitsOfShape (Discrete J) H] :
    ∃ K : QC 𝒪, Nonempty (preadditiveYoneda.obj K ≅ H) := sorry

section RightAdjoint

variable {D : Type uD} [Category.{vD} D]
  [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D] [_root_.CategoryTheory.IsTriangulated D]

/-- Proposition 21.43.9 (0GZ0) (3): an exact functor out of `QC 𝒪` which preserves
coproducts indexed in the coefficient universe has an exact right adjoint. -/
@[stacks 0GZ0 "(3)"]
theorem hasExactRightAdjoint
    (F : QC 𝒪 ⥤ D)
    [LocallySmall.{max (max (u + 1) (v + 1)) (w + 1)} D]
    [F.CommShift ℤ] [F.IsTriangulated]
    [∀ J : Type (max (max u v) w),
      PreservesColimitsOfShape (Discrete J) F] :
    ∃ (G : D ⥤ QC 𝒪) (adj : F ⊣ G),
      G.IsTriangulatedWith (adj.rightAdjointCommShift ℤ) := sorry

end RightAdjoint

/-- The canonical inclusion of `QC 𝒪` is a left adjoint.  Mathlib's chosen
`(inclusion 𝒪).rightAdjoint` is therefore available to downstream files. -/
@[stacks 0GZ0 "(4), right-adjoint existence"]
instance inclusionIsLeftAdjoint : (inclusion 𝒪).IsLeftAdjoint := sorry

/-- Proposition 21.43.9 (0GZ0) (4): the chosen right adjoint of the canonical inclusion is
triangulated for the shift comparison induced by its adjunction. -/
@[stacks 0GZ0 "(4), exact right adjoint"]
theorem inclusionRightAdjoint_isTriangulated :
    (inclusion 𝒪).rightAdjoint.IsTriangulatedWith
      ((Adjunction.ofIsLeftAdjoint (inclusion 𝒪)).rightAdjointCommShift ℤ) := sorry

end CategoryTheory.ModulesOnCategory.Chaotic
