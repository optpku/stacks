/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Prestable.Genus
import StacksCheckRecall

/-!
# Prestable curves of a given genus

The prestable locus decomposes into open-and-closed genus strata. Membership
is characterized by the rank of the first structure-sheaf higher direct image,
and over a field by nodality, dimension, canonical global functions, and genus.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.20.3 (1): every prestable family has a pairwise disjoint clopen
cover of its base representing the fixed-genus strata under cartesian base change. -/
@[stacks 0E6V] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_prestableOfGenus_clopen_decomposition :
    ∀ {S : Scheme.{u}} (P : Obj S), prestable S P →
      ∃ U : ℕ → (base P).left.Opens,
        iSup U = ⊤ ∧
          Pairwise (fun g g' ↦ Disjoint (U g : Set (base P).left) (U g')) ∧
            (∀ g, IsClopen (U g : Set (base P).left)) ∧
              ∀ g, ∀ {Q : Obj S} (φ : Q ⟶ P),
                prestableOfGenus g S Q ↔ Set.range (baseMap φ).left ⊆ U g)

/- Lemma 109.20.3 (2): a family belongs to the genus-g prestable stratum
precisely when it is prestable and its first higher direct image has rank g. -/
@[stacks 0E6V] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.prestableOfGenus_iff :
  ∀ (g : ℕ) {S : Scheme.{u}} (P : Obj S),
    prestableOfGenus g S P ↔ Prestable (hom P) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank g (higherDirectImageOne (hom P)))

/- Lemma 109.20.3 (3): a proper scheme of dimension at most one over a field
belongs to the genus-g prestable stratum precisely when it is at-worst-nodal,
has dimension one, has canonical global functions equal to the field, and has genus g. -/
@[stacks 0E6V] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_prestableOfGenus_iff_scheme :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1) (g : ℕ),
    prestableOfGenus g (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          SchemeOverField.genus X hdim1 hΓ = g)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
