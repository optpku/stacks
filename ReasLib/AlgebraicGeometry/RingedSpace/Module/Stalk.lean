/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Geometry.RingedSpace.Basic
public import Mathlib.Topology.Sheaves.Functors
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk.Exact
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Stalkwise exactness for module sheaves on ringed spaces

The generic exactness results live with `SheafOfModules`; this file provides the ergonomic
ringed-space specializations used by algebraic-geometry consumers.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace RingedSpace

/-- A sheaf of modules on a ringed space is zero exactly when all of its canonical stalk modules
are zero. -/
theorem isZero_iff_stalkModuleCat_isZero
    {X : RingedSpace.{u}} (ℱ : X.Modules) :
    IsZero ℱ ↔ ∀ x : X, IsZero (stalkModuleCat ℱ x) :=
  SheafOfModules.isZero_iff_stalkFunctorOfCommRing_obj_isZero X.sheaf ℱ

/-- A morphism of module sheaves on a ringed space is monic exactly when all of its canonical
stalk-module morphisms are monic. -/
theorem mono_iff_moduleStalkHom_mono
    {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    Mono f ↔ ∀ x : X, Mono (moduleStalkHom x f) :=
  SheafOfModules.mono_iff_stalkFunctorOfCommRing_map_mono X.sheaf f

/-- A morphism of module sheaves on a ringed space is epic exactly when all of its canonical
stalk-module morphisms are epic. -/
theorem epi_iff_moduleStalkHom_epi
    {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    Epi f ↔ ∀ x : X, Epi (moduleStalkHom x f) :=
  SheafOfModules.epi_iff_stalkFunctorOfCommRing_map_epi X.sheaf f

/-- A morphism of module sheaves on a ringed space is an isomorphism exactly when all of its
canonical stalk-module morphisms are isomorphisms. -/
theorem isIso_iff_moduleStalkHom_iso
    {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    IsIso f ↔ ∀ x : X, IsIso (moduleStalkHom x f) :=
  SheafOfModules.isIso_iff_stalkFunctorOfCommRing_map_iso X.sheaf f

/-- A morphism of module sheaves on a ringed space is monic exactly when all of its canonical
stalk-module maps are injective. -/
theorem mono_iff_moduleStalkMap_injective
    {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    Mono f ↔ ∀ x : X, Function.Injective (moduleStalkMap x f) :=
  SheafOfModules.mono_iff_stalkFunctorOfCommRing_map_injective X.sheaf f

/-- A morphism of module sheaves on a ringed space is epic exactly when all of its canonical
stalk-module maps are surjective. -/
theorem epi_iff_moduleStalkMap_surjective
    {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    Epi f ↔ ∀ x : X, Function.Surjective (moduleStalkMap x f) :=
  SheafOfModules.epi_iff_stalkFunctorOfCommRing_map_surjective X.sheaf f

/-- A morphism of module sheaves on a ringed space is an isomorphism exactly when all of its
canonical stalk-module maps are bijective. -/
theorem isIso_iff_moduleStalkMap_bijective
    {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    IsIso f ↔ ∀ x : X, Function.Bijective (moduleStalkMap x f) :=
  SheafOfModules.isIso_iff_stalkFunctorOfCommRing_map_bijective X.sheaf f

/-- A morphism of module sheaves on a ringed space is epic exactly when every canonical
stalk-module morphism has full range. -/
theorem epi_iff_moduleStalkHom_range_eq_top
    {X : RingedSpace.{u}} {ℱ 𝒢 : X.Modules} (f : ℱ ⟶ 𝒢) :
    Epi f ↔ ∀ x : X, (moduleStalkHom x f).hom.range = ⊤ :=
  SheafOfModules.epi_iff_stalkFunctorOfCommRing_map_range_eq_top X.sheaf f

/-- An exact short complex of module sheaves on a ringed space remains exact after taking the
stalk-module short complex at any point. -/
theorem moduleStalkShortComplex_exact
    {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (x : X) (hS : S.Exact) :
    (moduleStalkShortComplex S x).Exact :=
  SheafOfModules.stalkShortComplexOfCommRing_exact X.sheaf S x hS

/-- A short exact complex of module sheaves on a ringed space remains short exact after taking
the stalk-module short complex at any point. -/
@[stacks 01AG "short exactness is preserved by stalks"]
theorem moduleStalkShortComplex_shortExact
    {X : RingedSpace.{u}} (S : ShortComplex X.Modules) (x : X) (hS : S.ShortExact) :
    (moduleStalkShortComplex S x).ShortExact :=
  SheafOfModules.stalkShortComplexOfCommRing_shortExact X.sheaf S x hS

/-- Exactness of a short complex of module sheaves on a ringed space is detected by its
stalk-module short complexes. -/
@[stacks 01AG]
theorem exact_iff_moduleStalkShortComplex_exact
    {X : RingedSpace.{u}} (S : ShortComplex X.Modules) :
    S.Exact ↔ ∀ x : X, (moduleStalkShortComplex S x).Exact :=
  SheafOfModules.exact_iff_stalkShortComplexOfCommRing_exact X.sheaf S

/-- Short exactness of a complex of module sheaves on a ringed space is detected by its
stalk-module short complexes. -/
@[stacks 01AG "stalkwise criterion for short exactness"]
theorem shortExact_iff_moduleStalkShortComplex_shortExact
    {X : RingedSpace.{u}} (S : ShortComplex X.Modules) :
    S.ShortExact ↔ ∀ x : X, (moduleStalkShortComplex S x).ShortExact :=
  SheafOfModules.shortExact_iff_stalkShortComplexOfCommRing_shortExact X.sheaf S

end RingedSpace

end AlgebraicGeometry


