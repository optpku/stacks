/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap50.Situation_50_24_1
import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Pushforward.StructureSheaf.FiniteEtale
public import ReasLib.AlgebraicGeometry.Scheme.DeRham.StructureSheafPushforward
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

/- Lemma 50.24.2 (1): in Situation 50.24.1, the pushforward algebra
`f_*𝒪_X` is finite étale over `S`, expressed by an explicit relative-spectrum model. -/
@[stacks 0G8H]
#check (AlgebraicGeometry.Scheme.ModuleDerived.pushforwardStructureSheaf_finiteEtale : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n], (∀ s : S, Nonempty (f.fiber s)) → let A := Scheme.pushforwardStructureSheafQcAlgebra f; ∃ T : Scheme.RelativeSpectrumOver A, Scheme.IsRelativeSpectrumOver T ∧ IsFinite T.π ∧ Etale T.π)

/- Lemma 50.24.2 (2): in Situation 50.24.1, locally on `S` the derived
pushforward `Rf_*𝒪_X` is the direct sum of `f_*𝒪_X` in degree zero and a perfect
object of Tor amplitude in `[1, ∞)`. -/
@[stacks 0G8H]
#check (AlgebraicGeometry.Scheme.ModuleDerived.exists_local_structureSheafPushforward_decomposition_of_smooth : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n], (∀ s : S, Nonempty (f.fiber s)) → (s : S) → ∃ U : S.Opens, s ∈ U ∧ let g := f ∣_ U; let A := Scheme.pushforwardStructureSheafQcAlgebra g; ∃ P : RingedSpace.ModuleDerived U.toScheme.toRingedSpace, RingedSpace.ModuleDerived.IsPerfect P ∧ RingedSpace.HasTorAmplitudeGE P 1 ∧ IsIsomorphic ((RingedSpace.moduleDerivedPushforward g.toShHom).obj ((DerivedCategory.singleFunctor (f ⁻¹ᵁ U).toScheme.Modules 0).obj (SheafOfModules.unit (f ⁻¹ᵁ U).toScheme.toRingedSpace.ringCatSheaf))) (((DerivedCategory.singleFunctor U.toScheme.Modules 0).obj (Scheme.QcAlgebraUnder.underlyingModule U.toScheme A)) ⊞ P))

/- Lemma 50.24.2 (3): in Situation 50.24.1, the map
`f_*𝒪_X ⟶ f_*Ω¹_{X/S}` induced by the relative differential is zero. -/
@[stacks 0G8H]
#check (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforward_relativeDifferential_zero : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (n : ℕ) [CompactSpace S] [QuasiSeparatedSpace S] [IsProper f] [Smooth f] [Scheme.Hom.RelativeDimension f n], (∀ s : S, Nonempty (f.fiber s)) → (RingedSite.Hom.modulePushforward (AlgebraicGeometry.Scheme.DeRham.DerivedPushforward.pushforwardHom f)).map (RingedSpace.DeRham.d f.toLRSHom.toShHom 0) = 0)
