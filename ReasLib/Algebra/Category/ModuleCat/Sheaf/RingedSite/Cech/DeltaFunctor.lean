/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech.Exact
public import ReasLib.CategoryTheory.Homology.CohomologicalDeltaFunctor.ExactComplex
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cech cohomology as a delta functor

An exact ringed-site Cech complex on presheaf modules gives a cohomological delta functor by the
generic exact-complex construction. The geometric parameters only specialize that construction;
the long exact sequence machinery remains in `CohomologicalDeltaFunctor.ExactComplex`.
-/

@[expose] public section

open CategoryTheory Opposite
open CategoryTheory.Limits
open CategoryTheory.CohomologicalDeltaFunctor

noncomputable section

universe u v w

namespace SheafOfModules.RingedSite.Cech

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable (𝒪 : Sheaf J RingCat.{w}) (U : C) [HasFiniteProducts (Over U)]
variable {ι : Type w} (family : ι → Over U)

/-- The additive degree-`n` Cech cohomology functor on presheaf modules. -/
@[stacks 01EK "degreewise ringed-site module Cech cohomology"]
noncomputable abbrev degree (n : ℕ) :
    PresheafOfModules.{w} 𝒪.obj ⥤+ ModuleCat.{w} (𝒪.obj.obj (op U)) :=
  ExactComplex.degree (cechComplex 𝒪 U family) n

/-- A short exact sequence of presheaf modules gives a short exact sequence of Cech complexes. -/
theorem map_shortExact {S : ShortComplex (PresheafOfModules.{w} 𝒪.obj)}
    (hS : S.ShortExact) :
    (S.map (cechComplex 𝒪 U family)).ShortExact := sorry

/-- The Cech connecting morphism induced by a short exact sequence of presheaf modules. -/
noncomputable abbrev connecting
    {S : ShortComplex (PresheafOfModules.{w} 𝒪.obj)}
    (hS : S.ShortExact) (n : ℕ) :
    ((degree 𝒪 U family n).obj).obj S.X₃ ⟶
      ((degree 𝒪 U family (n + 1)).obj).obj S.X₁ :=
  ExactComplex.connecting (cechComplex 𝒪 U family)
    (cechComplex_exact 𝒪 U family) hS n

/-- Lemma 20.10.2 (Tag 01EK): Cech cohomology of presheaf modules is a cohomological delta
functor. -/
@[stacks 01EK "ringed-site module Cech delta functor"]
noncomputable def deltaFunctor :
    CohomologicalDeltaFunctor (PresheafOfModules.{w} 𝒪.obj)
      (ModuleCat.{w} (𝒪.obj.obj (op U))) :=
  ExactComplex.functor (cechComplex 𝒪 U family)
    (cechComplex_exact 𝒪 U family)

/-- The degree branches of `deltaFunctor` are the canonical Cech cohomology functors. -/
@[simp]
theorem deltaFunctor_obj (n : ℕ) :
    ((deltaFunctor 𝒪 U family n).obj) =
      cechComplex 𝒪 U family ⋙
        HomologicalComplex.homologyFunctor
          (ModuleCat.{w} (𝒪.obj.obj (op U))) (ComplexShape.up ℕ) n := sorry

/-- Evaluating a degree branch of `deltaFunctor` gives the corresponding Cech cohomology
object. -/
@[simp]
theorem deltaFunctor_obj_obj
    (n : ℕ) (M : PresheafOfModules.{w} 𝒪.obj) :
    ((deltaFunctor 𝒪 U family n).obj).obj M =
      cechCohomology 𝒪 U family M n := sorry

/-- The connecting map of `deltaFunctor` is the boundary map of the mapped short exact
sequence. -/
@[simp]
theorem deltaFunctor_δ
    {S : ShortComplex (PresheafOfModules.{w} 𝒪.obj)}
    (hS : S.ShortExact) (n : ℕ) :
    (deltaFunctor 𝒪 U family).δ hS n = connecting 𝒪 U family hS n := sorry

end SheafOfModules.RingedSite.Cech
