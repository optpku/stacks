module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Cech
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech.Sections
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections
import Mathlib.Tactic.CrossRefAttribute

/-!
# Low-degree Cech cohomology and injective coefficients

For modules on a ringed space, degree-zero Cech cohomology is sections on the union of the cover,
and injective coefficients have vanishing positive-degree Cech cohomology.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCech

variable {X : RingedSpace.{u}} {ι : Type u}

/-- Degree-zero Cech cohomology of a module sheaf is its additive group of sections on the union
of the indexed open family. -/
@[stacks 01EM "degree-zero additive Cech cohomology"]
theorem zero_isomorphic_sections
    (𝒰 : ι → Opens X.carrier) (F : X.Modules) :
    IsIsomorphic (moduleCechCohomology 𝒰 F 0)
      ((moduleSectionsAsAbelianFunctor X (iSup 𝒰)).obj F) := sorry

/-- Degree-zero Cech cohomology is naturally isomorphic to the sections functor on the union of
the indexed open family.  This functor-level form is the reusable bridge for delta-functor and
derived comparisons; it does not choose a particular representative isomorphism. -/
@[stacks 01EM "degree-zero Cech sections functor"]
theorem zero_isomorphic_sections_functor
    (𝒰 : ι → Opens X.carrier) :
    IsIsomorphic (moduleCechCohomologyFunctor 𝒰 0)
      (moduleSectionsAsAbelianFunctor X (iSup 𝒰)) := sorry

/-- Degree-zero Cech cohomology is identified with the module of sections on the covered open.
This is the module-valued geometric specialization of the ringed-site Cech owner. -/
@[stacks 01EM "degree-zero module Cech cohomology"]
theorem zero_isomorphic_evaluation
    (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    (F : X.Modules) :
    IsIsomorphic
      (cohomology U (Opens.Cover.overFamily U 𝒰 h𝒰) F 0)
      ((moduleSectionsEvaluationFunctor X U).obj F) := sorry

/-- The degree-zero module bridge in the injective-coefficient form used by the source lemma. -/
@[stacks 01EP "injective degree-zero module Cech cohomology"]
theorem zero_isomorphic_evaluation_of_injective
    (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    {I : X.Modules} [Injective I] :
    IsIsomorphic
      (cohomology U (Opens.Cover.overFamily U 𝒰 h𝒰) I 0)
      ((moduleSectionsEvaluationFunctor X U).obj I) := sorry

/-- Positive Cech cohomology of an injective module sheaf vanishes in module form. -/
@[stacks 01EP "injective positive-degree module Cech acyclicity"]
theorem isZero_of_injective_evaluation
    (U : Opens X.carrier) (𝒰 : ι → Opens X.carrier) (h𝒰 : iSup 𝒰 = U)
    {I : X.Modules} [Injective I] (p : ℕ) (hp : 0 < p) :
    IsZero (cohomology U (Opens.Cover.overFamily U 𝒰 h𝒰) I p) := sorry

/-- Positive-degree Cech cohomology of an injective module sheaf vanishes for every indexed open
family. -/
@[stacks 01EP "injective positive-degree Cech acyclicity"]
theorem isZero_of_injective
    (𝒰 : ι → Opens X.carrier) {I : X.Modules} [Injective I]
    {p : ℕ} (hp : 0 < p) :
    IsZero (moduleCechCohomology 𝒰 I p) := sorry

/-- Successor-degree form of injective module Cech acyclicity. -/
@[stacks 01EP "successor-degree injective Cech acyclicity"]
theorem isZero_succ_of_injective
    (𝒰 : ι → Opens X.carrier) {I : X.Modules} [Injective I] (p : ℕ) :
    IsZero (moduleCechCohomology 𝒰 I (p + 1)) := sorry

end AlgebraicGeometry.RingedSpace.ModuleCech
