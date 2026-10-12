/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Module.IdealPower.GlobalSections
import StacksCheckRecall

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

/- Lemma 28.25.3 (1): for a quasi-compact scheme, a finite-type ideal sheaf `I`, and a
quasi-coherent module sheaf `ℱ`, the canonical map from `colim_n Hom(I^n, ℱ)` to
`Γ(ℱ, I.openComplement)` is injective. -/
@[stacks 01PQ] #check
  (AlgebraicGeometry.Scheme.Modules.idealSheafPowerHomColimitToComplementSections_injective :
    ∀ {X : Scheme.{u}} [CompactSpace X.carrier]
      (I : X.IdealSheafData) (_ : I.IsFiniteType)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
        Function.Injective
          (AlgebraicGeometry.Scheme.Modules.idealSheafPowerHomColimitToComplementSections I ℱ).hom)

/- Lemma 28.25.3 (2): if the scheme is also quasi-separated, then the canonical map from
`colim_n Hom(I^n, ℱ / ℱ[I^n])` to `Γ(ℱ, I.openComplement)` is an isomorphism. -/
@[stacks 01PQ] #check
  (AlgebraicGeometry.Scheme.Modules.isIso_idealSheafPowerQuotientHomColimitToComplementSections :
    ∀ {X : Scheme.{u}} [CompactSpace X.carrier] [QuasiSeparatedSpace X.carrier]
      (I : X.IdealSheafData) (_ : I.IsFiniteType)
      (ℱ : X.Modules) [ℱ.IsQuasicoherent],
        IsIso (AlgebraicGeometry.Scheme.Modules.idealSheafPowerQuotientHomColimitToComplementSections I ℱ))
