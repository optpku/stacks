/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.SemistableLocus
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Spaces.Curves

/- Lemma 109.21.3: The semistable locus is open and classifies semistable families of curves. -/
@[stacks 0E70] #check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_semistable_open :
  ∀ {S : Scheme.{u}} (P : Obj S),
    ∃ U : (base P).left.Opens, ∀ {Q : Obj S} (φ : Q ⟶ P),
      semistable S Q ↔ Set.range (baseMap φ).left ⊆ U)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.semistable_iff :
  ∀ {S : Scheme.{u}} (P : Obj S),
    semistable S P ↔ AlgebraicSpace.Semistable (hom P))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.instIsClosedUnderIsomorphisms_semistable :
  ∀ S : Scheme.{u}, (semistable S).IsClosedUnderIsomorphisms)

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_semistable_iff_scheme :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    semistable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        ∃ (hdim1 : topologicalKrullDim X.left = 1)
          (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom)),
          1 ≤ SchemeOverField.genus X hdim1 hΓ ∧
            ¬ Nonempty (SchemeOverField.RationalTail X))

#check (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_semistable_iff_scheme_dualizing :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (hdim : topologicalKrullDim X.left ≤ 1),
    semistable (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      SchemeOverField.atWorstNodal X ∧
        topologicalKrullDim X.left = 1 ∧
        Function.Bijective (Scheme.Hom.globalSectionsMap X.hom) ∧
        dualizingTensorPowersGloballyGenerated X)

end AlgebraicGeometry.AlgebraicSpace.Spaces.Curves
