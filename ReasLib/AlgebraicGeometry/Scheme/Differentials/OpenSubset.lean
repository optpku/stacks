module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Pullback.Differentials
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Restriction of relative differentials on schemes

For opens `U ⊆ X` and `V ⊆ S` such that `f(U) ⊆ V`, the canonical square of open
immersions induces the comparison from the restriction of `Ω_{X/S}` to `Ω_{U/V}`.  This file
owns that concrete comparison and records that it is an isomorphism.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.RelativeDifferentials.OpenSubset

variable {X S : Scheme.{u}} (f : X ⟶ S)
variable (U : X.Opens) (V : S.Opens) (hU : U ≤ f ⁻¹ᵁ V)

/-- The restriction of `f` from `U` to `V`, under the hypothesis `f(U) ⊆ V`. -/
abbrev restrictedMap : U.toScheme ⟶ V.toScheme :=
  X.homOfLE hU ≫ f ∣_ V

/-- The open immersions and `restrictedMap` form the canonical commutative square over `f`. -/
theorem commSq :
    CommSq
      (X.ofRestrict U.isOpenEmbedding).toShHom
      (restrictedMap f U V hU).toShHom
      f.toShHom
      (S.ofRestrict V.isOpenEmbedding).toShHom := sorry

/-- The canonical comparison from the restriction of `Ω_{X/S}` to `Ω_{U/V}`. -/
noncomputable abbrev comparison :
    (RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding).toShHom).obj
        Ω[f.toShHom] ⟶
      Ω[(restrictedMap f U V hU).toShHom] :=
  RingedSpace.Hom.Differentials.comparison (commSq f U V hU)

/-- The open-restriction comparison for relative differentials is an isomorphism. -/
instance comparison_isIso : IsIso (comparison f U V hU) := sorry

/-- The open-restriction comparison carries universal differentials to the corresponding
restricted universal differentials. -/
theorem comparison_spec :
    RingedSpace.Hom.Differentials.IsComparison (comparison f U V hU) := sorry

/-- A morphism compatible with universal differentials is the canonical open-restriction
comparison. -/
theorem eq_comparison
    {τ :
      (RingedSpace.Hom.pullback (X.ofRestrict U.isOpenEmbedding).toShHom).obj
          Ω[f.toShHom] ⟶
        Ω[(restrictedMap f U V hU).toShHom]}
    (hτ : RingedSpace.Hom.Differentials.IsComparison τ) :
    τ = comparison f U V hU := sorry

end AlgebraicGeometry.Scheme.RelativeDifferentials.OpenSubset
