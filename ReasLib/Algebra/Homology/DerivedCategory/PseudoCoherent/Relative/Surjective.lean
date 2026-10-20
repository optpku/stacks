module

public import Mathlib.Data.List.TFAE
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat.Restriction
public import ReasLib.Algebra.Homology.DerivedCategory.PseudoCoherent.Relative.ChangeOfBase
public import ReasLib.RingTheory.RingHom.Perfect.Flat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Relative pseudo-coherence across a surjection

For a surjective map, relative pseudo-coherence over the source is the absolute
pseudo-coherence of the restricted derived object.  Combined with flat finite-presentation
hypotheses over a common base, this gives the five equivalent forms used in change of rings.

@stack 0E1T
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory.DerivedCategory

/-- For a surjective algebra map, relative `m`-pseudo-coherence over the source is equivalent to
absolute `m`-pseudo-coherence after derived restriction of scalars. -/
@[stacks 0E1T "surjective restriction criterion for relative m-pseudo-coherence"]
theorem isMPseudoCoherentRelativeTo_iff_restrictScalars_of_surjective
    {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    (K : DerivedCategory (ModuleCat A)) (m : ℤ)
    (hφ : Function.Surjective (algebraMap B A)) :
    let _ : Algebra.FiniteType B A :=
      Algebra.FiniteType.of_surjective (Algebra.ofId B A) hφ
    K.IsMPseudoCoherentRelativeTo B m ↔
      ((ModuleCat.derivedRestrictionOfScalars (algebraMap B A)).obj K).IsMPseudoCoherent m := sorry
/- Proof strategy: use the zero-variable presentation of `A` supplied by the surjection and the
displayed finite-type instance; identify restriction along that presentation with
`ModuleCat.derivedRestrictionOfScalars (algebraMap B A)`. -/

/-- For a surjective algebra map, relative pseudo-coherence over the source is equivalent to
absolute pseudo-coherence after derived restriction of scalars. -/
@[stacks 0E1T "surjective restriction criterion for relative pseudo-coherence"]
theorem isPseudoCoherentRelativeTo_iff_restrictScalars_of_surjective
    {B A : Type u} [CommRing B] [CommRing A] [Algebra B A]
    (K : DerivedCategory (ModuleCat A))
    (hφ : Function.Surjective (algebraMap B A)) :
    let _ : Algebra.FiniteType B A :=
      Algebra.FiniteType.of_surjective (Algebra.ofId B A) hφ
    K.IsPseudoCoherentRelativeTo B ↔
      ((ModuleCat.derivedRestrictionOfScalars (algebraMap B A)).obj K).IsPseudoCoherent := sorry
/- Proof strategy: apply the surjective `m`-pseudo-coherence criterion at every integer bound and
unfold relative and absolute pseudo-coherence. -/

/-- Lemma 15.83.8 (1): for a surjection `B → A`, when `R → B` and `R → A` are flat
and finitely presented, the five absolute, relative, and restricted forms of pseudo-coherence
are equivalent. -/
@[stacks 0E1T "(1), pseudo-coherence across a surjective change of rings"]
theorem pseudoCoherent_tfae_of_surjective_of_flat_finitePresentation
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A))
    (hφ : Function.Surjective (algebraMap B A)) :
    List.TFAE [
      K.IsPseudoCoherent,
      K.IsPseudoCoherentRelativeTo R,
      K.IsPseudoCoherentRelativeTo A,
      ((ModuleCat.derivedRestrictionOfScalars (algebraMap B A)).obj K).IsPseudoCoherent,
      ((ModuleCat.derivedRestrictionOfScalars
        (algebraMap B A)).obj K).IsPseudoCoherentRelativeTo R
    ] := sorry
/- Proof strategy: prove the five-cycle with `List.TFAE.out`. Use the perfect, hence
pseudo-coherent, instances for the flat finitely presented maps `R → B` and `R → A`; combine the
relative/absolute comparison, intermediate-base change, and the surjective restriction criterion. -/

/-- Lemma 15.83.8 (2): under the same hypotheses, the five absolute, relative, and restricted
forms of `m`-pseudo-coherence are equivalent. -/
@[stacks 0E1T "(2), m-pseudo-coherence across a surjective change of rings"]
theorem mPseudoCoherent_tfae_of_surjective_of_flat_finitePresentation
    {R B A : Type u} [CommRing R] [CommRing B] [CommRing A]
    [Algebra R B] [Algebra B A] [Algebra R A] [IsScalarTower R B A]
    [Module.Flat R B] [Algebra.FinitePresentation R B]
    [Module.Flat R A] [Algebra.FinitePresentation R A]
    (K : DerivedCategory (ModuleCat A)) (m : ℤ)
    (hφ : Function.Surjective (algebraMap B A)) :
    List.TFAE [
      K.IsMPseudoCoherent m,
      K.IsMPseudoCoherentRelativeTo R m,
      K.IsMPseudoCoherentRelativeTo A m,
      ((ModuleCat.derivedRestrictionOfScalars (algebraMap B A)).obj K).IsMPseudoCoherent m,
      ((ModuleCat.derivedRestrictionOfScalars
        (algebraMap B A)).obj K).IsMPseudoCoherentRelativeTo R m
    ] := sorry
/- Proof strategy: follow the same `List.TFAE` cycle as the pseudo-coherent case, using the
`m`-versions of relative/absolute comparison, change of intermediate base, and surjective derived
restriction. -/

end CategoryTheory.DerivedCategory
