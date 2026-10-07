module

public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.Derived
public import ReasLib.RingTheory.RingHom.PseudoCoherent.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Change of base for relative pseudo-coherence

The comparison results in this file distinguish an explicit finite-type tower
from the special case supplied by a pseudo-coherent ring map.

@stack 0673
@stack 0DHQ
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u v w

namespace CategoryTheory.DerivedCategory

/-- Lemma 15.82.5 (1): restriction along a finite map of finite-type algebras preserves and
reflects relative `m`-pseudo-coherence. -/
@[stacks 0673 "(1), finite scalar restriction"]
theorem isMPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B]
    (K : DerivedCategory (ModuleCat B)) (m : ℤ) :
    let _ : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A B)
    K.IsMPseudoCoherentRelativeTo R m ↔
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K).IsMPseudoCoherentRelativeTo R m := sorry
/- Proof strategy: test both sides on an arbitrary finite polynomial presentation over `R`, then
apply finite restriction of scalars for `m`-pseudo-coherent complexes along `A → B`; use
`Module.Finite A B` and the composite finite-type witness displayed in the statement. -/

/-- Lemma 15.82.5 (2): restriction along a finite map of finite-type algebras preserves and
reflects relative pseudo-coherence. -/
@[stacks 0673 "(2), finite scalar restriction"]
theorem isPseudoCoherentRelativeTo_iff_restrictScalars_of_finite
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Module.Finite A B]
    (K : DerivedCategory (ModuleCat B)) :
    let _ : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A B)
    K.IsPseudoCoherentRelativeTo R ↔
      ((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory.obj K).IsPseudoCoherentRelativeTo R := sorry
/- Proof strategy: unfold relative pseudo-coherence into its family of integer bounds and apply
`isMPseudoCoherentRelativeTo_iff_restrictScalars_of_finite` at every bound. -/

/-- Lemma 15.82.15 (1): relative `m`-pseudo-coherence over an intermediate finite type algebra
agrees with relative `m`-pseudo-coherence over the base when the intermediate regular module is
pseudo-coherent relative to that base. -/
@[stacks 067D "(1), intermediate-base relative m-pseudo-coherence"]
theorem isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
    {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType A B] [Algebra.FiniteType R B]
    (K : DerivedCategory (ModuleCat B)) (m : ℤ)
    (h_A : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    K.IsMPseudoCoherentRelativeTo A m ↔ K.IsMPseudoCoherentRelativeTo R m := sorry
/- Proof strategy: compare finite polynomial presentations over `R` and `A`. The hypothesis `h_A`
controls the change of polynomial base, and transitivity of relative `m`-pseudo-coherence gives
both implications after derived restriction to the common presentation ring. -/

/-- Lemma 15.82.15 (2): relative pseudo-coherence over an intermediate finite type algebra
agrees with relative pseudo-coherence over the base when the intermediate regular module is
pseudo-coherent relative to that base. -/
@[stacks 067D "(2), intermediate-base relative pseudo-coherence"]
theorem isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo
    {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType A B] [Algebra.FiniteType R B]
    (K : DerivedCategory (ModuleCat B))
    (h_A : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    K.IsPseudoCoherentRelativeTo A ↔ K.IsPseudoCoherentRelativeTo R := sorry
/- Proof strategy: apply the preceding intermediate-base comparison for every integer bound and
reassemble the definition of relative pseudo-coherence. -/

/-- The finite-type-tower form of the intermediate-base comparison installs the canonical
finite-type structure on the composite algebra internally. Mathlib intentionally does not
register transitivity of `Algebra.FiniteType` as a global instance; the local witness pins the
unique composite proof only at this bridge and avoids a global search loop. -/
@[stacks 067D "intermediate-base relative m-pseudo-coherence for a tower"]
theorem isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo_of_tower
    {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType A B]
    (K : DerivedCategory (ModuleCat B)) (m : ℤ)
    (h_A : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    let _ : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A B)
    K.IsMPseudoCoherentRelativeTo A m ↔ K.IsMPseudoCoherentRelativeTo R m := sorry
/- Proof strategy: install the displayed composite finite-type structure and apply
`isMPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo`; only the
definitional pin for `Algebra.FiniteType R B` remains. -/

/-- The finite-type-tower form of the pseudo-coherence comparison installs the canonical
finite-type structure on the composite algebra internally. The local witness is a definitional
pin for that composite structure, not a new mathematical choice. -/
@[stacks 067D "intermediate-base relative pseudo-coherence for a tower"]
theorem isPseudoCoherentRelativeTo_iff_of_intermediate_isPseudoCoherentRelativeTo_of_tower
    {R : Type u} {A : Type v} {B : Type w} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [Algebra.FiniteType R A] [Algebra.FiniteType A B]
    (K : DerivedCategory (ModuleCat B))
    (h_A : (ModuleCat.of A A).IsPseudoCoherentRelativeTo R) :
    let _ : Algebra.FiniteType R B :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R A)
        (inferInstance : Algebra.FiniteType A B)
    K.IsPseudoCoherentRelativeTo A ↔ K.IsPseudoCoherentRelativeTo R := sorry
/- Proof strategy: install the same composite finite-type witness and invoke the unbounded
intermediate-base comparison. -/

/-- Lemma 15.83.7 (1): over a pseudo-coherent ring map, relative `m`-pseudo-coherence agrees
with absolute `m`-pseudo-coherence. -/
@[stacks 0DHQ "(1), relative and absolute m-pseudo-coherence"]
theorem isMPseudoCoherentRelativeTo_iff_isMPseudoCoherent_of_isPseudoCoherentRingMap
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [(algebraMap R A).IsPseudoCoherentRingMap]
    (K : DerivedCategory (ModuleCat A)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo R m ↔ K.IsMPseudoCoherent m := sorry
/- Proof strategy: obtain relative pseudo-coherence of the target regular module from
`Algebra.targetRegularModule_isPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`, apply the
intermediate-base comparison with intermediate ring `A`, and identify relative coherence over
`A` with absolute coherence using the self comparison. -/

/-- Lemma 15.83.7 (2): over a pseudo-coherent ring map, relative pseudo-coherence agrees with
absolute pseudo-coherence. -/
@[stacks 0DHQ "(2), relative and absolute pseudo-coherence"]
theorem isPseudoCoherentRelativeTo_iff_isPseudoCoherent_of_isPseudoCoherentRingMap
    {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
    [(algebraMap R A).IsPseudoCoherentRingMap]
    (K : DerivedCategory (ModuleCat A)) :
    K.IsPseudoCoherentRelativeTo R ↔ K.IsPseudoCoherent := sorry
/- Proof strategy: repeat the preceding argument with the unbounded intermediate-base theorem, or
apply its `m`-version at every bound. -/

/-- Relative `m`-pseudo-coherence over a ring itself is absolute `m`-pseudo-coherence. -/
@[stacks 0DHQ "relative m-pseudo-coherence over the base ring itself"]
theorem isMPseudoCoherentRelativeTo_self_iff
    {A : Type u} [CommRing A] (K : DerivedCategory (ModuleCat A)) (m : ℤ) :
    K.IsMPseudoCoherentRelativeTo A m ↔ K.IsMPseudoCoherent m := sorry
/- Proof strategy: use the identity finite polynomial presentation and the derived restriction
functor for `RingHom.id A`; simplify that functor to the identity and unfold the absolute
`m`-pseudo-coherence predicate. -/

/-- Relative pseudo-coherence over a ring itself is absolute pseudo-coherence. -/
@[stacks 0DHQ "relative pseudo-coherence over the base ring itself"]
theorem isPseudoCoherentRelativeTo_self_iff
    {A : Type u} [CommRing A] (K : DerivedCategory (ModuleCat A)) :
    K.IsPseudoCoherentRelativeTo A ↔ K.IsPseudoCoherent := sorry
/- Proof strategy: apply `isMPseudoCoherentRelativeTo_self_iff` for every integer bound and unfold
the two unbounded pseudo-coherence predicates. -/

end CategoryTheory.DerivedCategory

namespace CategoryTheory.DerivedCategory

end CategoryTheory.DerivedCategory
