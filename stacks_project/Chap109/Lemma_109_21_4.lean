/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Semistable.Genus
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.ObjectProperty
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.21.4 (1): the semistable curve locus decomposes into
pairwise disjoint open-and-closed positive-genus loci. -/
@[stacks 0E71] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_semistableOfGenus_clopen_decomposition
    : ∀ {S : Scheme.{u}} (P : Obj S)
    (h : semistable S P),
    ∃ U : ℕ → (base P).left.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun n n' ↦ Disjoint (U n : Set (base P).left) (U n')) ∧
          (∀ n, IsClopen (U n : Set (base P).left)) ∧
            ∀ n, ∀ {Q : Obj S} (φ : Q ⟶ P),
              semistableOfGenus (n + 1) S Q ↔ Set.range (baseMap φ).left ⊆ U n)

/- Lemma 109.21.4 (2): a family belongs to the genus-`g` locus precisely
when it is semistable and `R¹ f_* 𝒪_X` is finite locally free of rank `g`. -/
@[stacks 0E71] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.semistableOfGenus_iff
    : ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    semistableOfGenus g S P ↔
      semistable S P ∧
        SheafOfModules.IsFiniteLocallyFreeOfRank g
          (higherDirectImageOne (hom P)))

/- Lemma 109.21.4 (3): over a field, the genus-`g` locus is characterized
by nodality, dimension one, constant global functions, genus `g`, and no
rational tails. -/
@[stacks 0E71] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_semistableOfGenus_iff_scheme
    : ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 1 ≤ g),
    semistableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g ∧
            ¬ Nonempty (SchemeOverField.RationalTail X))

/- Lemma 109.21.4 (4): over a field, the genus-`g` locus is characterized
by nodality, dimension one, constant global functions, genus `g`, and global
generation of all dualizing tensor powers of exponent at least two. -/
@[stacks 0E71] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_semistableOfGenus_iff_scheme_dualizing
    : ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ) (hg : 1 ≤ g),
    semistableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g ∧
            dualizingTensorPowersGloballyGenerated X)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
