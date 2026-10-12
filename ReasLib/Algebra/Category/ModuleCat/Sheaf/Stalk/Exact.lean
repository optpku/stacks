/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# Exactness detected on module stalks

The generic `SheafOfModules` results in this file isolate finite-(co)limit preservation and the
stalkwise criteria for zero objects, mono/epi/isomorphisms, and short exact sequences.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

universe u

namespace SheafOfModules

section Forgetful

universe w r v

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- Forgetting a sheaf of modules to its underlying sheaf of additive groups preserves finite
colimits. Together with mathlib's finite-limit preservation instance, this makes
`SheafOfModules.toSheaf` an exact functor at the canonical site-theoretic level. -/
noncomputable instance toSheaf_preservesFiniteColimits
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (𝒪 : Sheaf J RingCat.{r}) :
    PreservesFiniteColimits (toSheaf.{w} 𝒪) := sorry

end Forgetful

variable {Z : TopCat.{u}}

/-- Taking stalks of module sheaves over a ring sheaf preserves finite limits. -/
instance stalkFunctor_preservesFiniteLimits
    (𝒪 : Z.Sheaf RingCat.{u}) (x : Z) :
    PreservesFiniteLimits (stalkFunctor 𝒪 x) := sorry

/-- Taking stalks of module sheaves over a ring sheaf preserves finite colimits. -/
instance stalkFunctor_preservesFiniteColimits
    (𝒪 : Z.Sheaf RingCat.{u}) (x : Z) :
    PreservesFiniteColimits (stalkFunctor 𝒪 x) := sorry

/-- A sheaf of modules over a ring sheaf is zero exactly when all of its stalk modules are zero. -/
theorem isZero_iff_stalkFunctor_obj_isZero
    (𝒪 : Z.Sheaf RingCat.{u}) (ℱ : SheafOfModules 𝒪) :
    IsZero ℱ ↔ ∀ x : Z, IsZero ((stalkFunctor 𝒪 x).obj ℱ) := sorry

/-- A morphism of module sheaves over a ring sheaf is monic exactly when all of its stalk-module
morphisms are monic. -/
theorem mono_iff_stalkFunctor_map_mono
    (𝒪 : Z.Sheaf RingCat.{u}) {ℱ 𝒢 : SheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) :
    Mono f ↔ ∀ x : Z, Mono ((stalkFunctor 𝒪 x).map f) := sorry

/-- A morphism of module sheaves over a ring sheaf is epic exactly when all of its stalk-module
morphisms are epic. -/
theorem epi_iff_stalkFunctor_map_epi
    (𝒪 : Z.Sheaf RingCat.{u}) {ℱ 𝒢 : SheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) :
    Epi f ↔ ∀ x : Z, Epi ((stalkFunctor 𝒪 x).map f) := sorry

/-- A morphism of module sheaves over a ring sheaf is an isomorphism exactly when all of its
stalk-module morphisms are isomorphisms. -/
theorem isIso_iff_stalkFunctor_map_iso
    (𝒪 : Z.Sheaf RingCat.{u}) {ℱ 𝒢 : SheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) :
    IsIso f ↔ ∀ x : Z, IsIso ((stalkFunctor 𝒪 x).map f) := sorry

/-- A morphism of module sheaves over a ring sheaf is monic exactly when all of its stalk-module
maps are injective. -/
theorem mono_iff_stalkFunctor_map_injective
    (𝒪 : Z.Sheaf RingCat.{u}) {ℱ 𝒢 : SheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) :
    Mono f ↔ ∀ x : Z, Function.Injective (((stalkFunctor 𝒪 x).map f).hom) := sorry

/-- A morphism of module sheaves over a ring sheaf is epic exactly when all of its stalk-module
maps are surjective. -/
theorem epi_iff_stalkFunctor_map_surjective
    (𝒪 : Z.Sheaf RingCat.{u}) {ℱ 𝒢 : SheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) :
    Epi f ↔ ∀ x : Z, Function.Surjective (((stalkFunctor 𝒪 x).map f).hom) := sorry

/-- A morphism of module sheaves over a ring sheaf is an isomorphism exactly when all of its
stalk-module maps are bijective. -/
theorem isIso_iff_stalkFunctor_map_bijective
    (𝒪 : Z.Sheaf RingCat.{u}) {ℱ 𝒢 : SheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) :
    IsIso f ↔ ∀ x : Z, Function.Bijective (((stalkFunctor 𝒪 x).map f).hom) := sorry

/-- A morphism of module sheaves over a ring sheaf is epic exactly when every stalk-module map
has full range. -/
theorem epi_iff_stalkFunctor_map_range_eq_top
    (𝒪 : Z.Sheaf RingCat.{u}) {ℱ 𝒢 : SheafOfModules 𝒪} (f : ℱ ⟶ 𝒢) :
    Epi f ↔ ∀ x : Z, ((stalkFunctor 𝒪 x).map f).hom.range = ⊤ := sorry

/-- Taking stalks of module sheaves over the underlying ring sheaf of a commutative-ring sheaf
preserves finite limits. -/
instance stalkFunctorOfCommRing_preservesFiniteLimits
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) :
    PreservesFiniteLimits (stalkFunctorOfCommRing 𝒪 x) := sorry

/-- Taking stalks of module sheaves over the underlying ring sheaf of a commutative-ring sheaf
preserves finite colimits. -/
instance stalkFunctorOfCommRing_preservesFiniteColimits
    (𝒪 : Z.Sheaf CommRingCat.{u}) (x : Z) :
    PreservesFiniteColimits (stalkFunctorOfCommRing 𝒪 x) := sorry

/-- A sheaf of modules over the underlying ring sheaf of a commutative-ring sheaf is zero exactly
when all of its stalk modules are zero. -/
theorem isZero_iff_stalkFunctorOfCommRing_obj_isZero
    (𝒪 : Z.Sheaf CommRingCat.{u})
    (ℱ : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)) :
    IsZero ℱ ↔ ∀ x : Z, IsZero ((stalkFunctorOfCommRing 𝒪 x).obj ℱ) := sorry

/-- A morphism of module sheaves over the underlying ring sheaf of a commutative-ring sheaf is
monic exactly when all of its stalk-module morphisms are monic. -/
theorem mono_iff_stalkFunctorOfCommRing_map_mono
    (𝒪 : Z.Sheaf CommRingCat.{u})
    {ℱ 𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)} (f : ℱ ⟶ 𝒢) :
    Mono f ↔ ∀ x : Z, Mono ((stalkFunctorOfCommRing 𝒪 x).map f) := sorry

/-- A morphism of module sheaves over the underlying ring sheaf of a commutative-ring sheaf is
epic exactly when all of its stalk-module morphisms are epic. -/
theorem epi_iff_stalkFunctorOfCommRing_map_epi
    (𝒪 : Z.Sheaf CommRingCat.{u})
    {ℱ 𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)} (f : ℱ ⟶ 𝒢) :
    Epi f ↔ ∀ x : Z, Epi ((stalkFunctorOfCommRing 𝒪 x).map f) := sorry

/-- A morphism of module sheaves over the underlying ring sheaf of a commutative-ring sheaf is an
isomorphism exactly when all of its stalk-module morphisms are isomorphisms. -/
theorem isIso_iff_stalkFunctorOfCommRing_map_iso
    (𝒪 : Z.Sheaf CommRingCat.{u})
    {ℱ 𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)} (f : ℱ ⟶ 𝒢) :
    IsIso f ↔ ∀ x : Z, IsIso ((stalkFunctorOfCommRing 𝒪 x).map f) := sorry

/-- A morphism of module sheaves over the underlying ring sheaf of a commutative-ring sheaf is
monic exactly when all of its stalk-module maps are injective. -/
theorem mono_iff_stalkFunctorOfCommRing_map_injective
    (𝒪 : Z.Sheaf CommRingCat.{u})
    {ℱ 𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)} (f : ℱ ⟶ 𝒢) :
    Mono f ↔ ∀ x : Z, Function.Injective (((stalkFunctorOfCommRing 𝒪 x).map f).hom) := sorry

/-- A morphism of module sheaves over the underlying ring sheaf of a commutative-ring sheaf is
epic exactly when all of its stalk-module maps are surjective. -/
theorem epi_iff_stalkFunctorOfCommRing_map_surjective
    (𝒪 : Z.Sheaf CommRingCat.{u})
    {ℱ 𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)} (f : ℱ ⟶ 𝒢) :
    Epi f ↔ ∀ x : Z, Function.Surjective (((stalkFunctorOfCommRing 𝒪 x).map f).hom) := sorry

/-- A morphism of module sheaves over the underlying ring sheaf of a commutative-ring sheaf is an
isomorphism exactly when all of its stalk-module maps are bijective. -/
theorem isIso_iff_stalkFunctorOfCommRing_map_bijective
    (𝒪 : Z.Sheaf CommRingCat.{u})
    {ℱ 𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)} (f : ℱ ⟶ 𝒢) :
    IsIso f ↔ ∀ x : Z, Function.Bijective (((stalkFunctorOfCommRing 𝒪 x).map f).hom) := sorry

/-- A morphism of module sheaves over the underlying ring sheaf of a commutative-ring sheaf is
epic exactly when every stalk-module map has full range. -/
theorem epi_iff_stalkFunctorOfCommRing_map_range_eq_top
    (𝒪 : Z.Sheaf CommRingCat.{u})
    {ℱ 𝒢 : SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪)} (f : ℱ ⟶ 𝒢) :
    Epi f ↔ ∀ x : Z, ((stalkFunctorOfCommRing 𝒪 x).map f).hom.range = ⊤ := sorry

/-- An exact short complex of module sheaves over a ring sheaf remains exact after taking any
stalk. -/
theorem stalkShortComplex_exact
    (𝒪 : Z.Sheaf RingCat.{u}) (S : ShortComplex (SheafOfModules 𝒪)) (x : Z)
    (hS : S.Exact) :
    (stalkShortComplex 𝒪 S x).Exact := sorry

/-- A short exact complex of module sheaves over a ring sheaf remains short exact after taking
any stalk. -/
theorem stalkShortComplex_shortExact
    (𝒪 : Z.Sheaf RingCat.{u}) (S : ShortComplex (SheafOfModules 𝒪)) (x : Z)
    (hS : S.ShortExact) :
    (stalkShortComplex 𝒪 S x).ShortExact := sorry

/-- Exactness of a short complex of module sheaves over a ring sheaf is detected by its stalk
module short complexes. -/
theorem exact_iff_stalkShortComplex_exact
    (𝒪 : Z.Sheaf RingCat.{u}) (S : ShortComplex (SheafOfModules 𝒪)) :
    S.Exact ↔ ∀ x : Z, (stalkShortComplex 𝒪 S x).Exact := sorry

/-- Short exactness of a complex of module sheaves over a ring sheaf is detected by its stalk
module short complexes. -/
theorem shortExact_iff_stalkShortComplex_shortExact
    (𝒪 : Z.Sheaf RingCat.{u}) (S : ShortComplex (SheafOfModules 𝒪)) :
    S.ShortExact ↔ ∀ x : Z, (stalkShortComplex 𝒪 S x).ShortExact := sorry

/-- An exact short complex over the underlying ring sheaf of a commutative-ring sheaf remains
exact after taking any stalk. -/
theorem stalkShortComplexOfCommRing_exact
    (𝒪 : Z.Sheaf CommRingCat.{u})
    (S : ShortComplex (SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪))) (x : Z)
    (hS : S.Exact) :
    (stalkShortComplexOfCommRing 𝒪 S x).Exact := sorry

/-- A short exact complex over the underlying ring sheaf of a commutative-ring sheaf remains
short exact after taking any stalk. -/
theorem stalkShortComplexOfCommRing_shortExact
    (𝒪 : Z.Sheaf CommRingCat.{u})
    (S : ShortComplex (SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪))) (x : Z)
    (hS : S.ShortExact) :
    (stalkShortComplexOfCommRing 𝒪 S x).ShortExact := sorry

/-- Exactness of a short complex over the underlying ring sheaf of a commutative-ring sheaf is
detected by its stalk-module short complexes. -/
theorem exact_iff_stalkShortComplexOfCommRing_exact
    (𝒪 : Z.Sheaf CommRingCat.{u})
    (S : ShortComplex (SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪))) :
    S.Exact ↔ ∀ x : Z, (stalkShortComplexOfCommRing 𝒪 S x).Exact := sorry

/-- Short exactness of a complex over the underlying ring sheaf of a commutative-ring sheaf is
detected by its stalk-module short complexes. -/
theorem shortExact_iff_stalkShortComplexOfCommRing_shortExact
    (𝒪 : Z.Sheaf CommRingCat.{u})
    (S : ShortComplex (SheafOfModules (TopCat.Sheaf.ringSheafOfComm 𝒪))) :
    S.ShortExact ↔ ∀ x : Z, (stalkShortComplexOfCommRing 𝒪 S x).ShortExact := sorry

end SheafOfModules
