/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Sections
public import ReasLib.Algebra.Module.IdealPower.Quotient
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.PullbackSections
public import ReasLib.CategoryTheory.InverseSystem.MittagLeffler

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SequentialInverseSystem Opposite
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- The `n`th projection from the limit of formal global sections kills
`S.I ^ n • sectionsLimit S F`. -/
theorem sectionsLimitProjection_power_le_ker (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ) :
    S.I ^ n • (⊤ : Submodule A (sectionsLimit S F)) ≤
      LinearMap.ker (limit.π (sectionsSystem S F) (op n)).hom := sorry

/-- The canonical map from `sectionsLimit S F / S.I ^ n sectionsLimit S F` to the
`n`th module of global sections, obtained by descending the limit projection. -/
noncomputable def sectionsQuotientProjection (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ) :
    Ideal.PowerQuotient.stage S.I (sectionsLimit S F) n ⟶
      (sectionsSystem S F).obj (op n) :=
  ConcreteCategory.ofHom
    (Submodule.liftQ (S.I ^ n • (⊤ : Submodule A (sectionsLimit S F)))
      (limit.π (sectionsSystem S F) (op n)).hom
      (sectionsLimitProjection_power_le_ker S F n))

/-- Precomposing `sectionsQuotientProjection S F n` with the quotient map recovers the
`n`th limit projection. -/
theorem sectionsQuotientProjection_fac (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ) :
    ModuleCat.ofHom (Submodule.mkQ
        (S.I ^ n • (⊤ : Submodule A (sectionsLimit S F)))) ≫
      sectionsQuotientProjection S F n = limit.π (sectionsSystem S F) (op n) := sorry

/-- The canonical sheaf morphism from the restriction to `S.U` of the tilde sheaf of
`sectionsLimit S F / S.I ^ n sectionsLimit S F` to the `n`th formal-module stage. -/
noncomputable def sectionsComparison (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ) :
    (Scheme.Modules.pullback S.U.ι).obj
        (AlgebraicGeometry.tilde (Ideal.PowerQuotient.stage S.I (sectionsLimit S F) n)) ⟶
      (F.obj.obj (op n)).obj :=
  Scheme.Modules.pullbackTildeHom S.U.ι
    (Ideal.PowerQuotient.stage S.I (sectionsLimit S F) n) (F.obj.obj (op n)).obj
    (sectionsQuotientProjection S F n)

/-- Under the pullback-tilde/global-sections adjunction, `sectionsComparison S F n` is
the quotient-stage projection `sectionsQuotientProjection S F n`. -/
theorem sectionsComparison_spec (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) (n : ℕ) :
    Scheme.Modules.pullbackTildeHomEquiv S.U.ι
        (Ideal.PowerQuotient.stage S.I (sectionsLimit S F) n) (F.obj.obj (op n)).obj
        (sectionsComparison S F n) =
      sectionsQuotientProjection S F n := sorry

/-- If the inverse system of global sections of a coherent formal module satisfies the
Mittag-Leffler condition, every canonical sheaf comparison from the restricted tilde sheaf
of the corresponding quotient of its section limit is an epimorphism. -/
@[stacks 0EHF]
theorem sectionsComparison_epi (S : AffineAlgebraizationSetup A)
    (F : CoherentFormalModules S.U.toScheme
      ((Scheme.idealSheafDataOfIdealOnSpec S.I).comap S.U.ι)) :
    IsMittagLeffler (sectionsSystem S F) →
      ∀ n : ℕ, Epi (sectionsComparison S F n) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
