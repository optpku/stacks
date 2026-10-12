/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.PerfectClosure
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open scoped PerfectClosure

universe u

/- Lemma 58.14.2 (1): the base change of a connected scheme to the perfect closure of its
base field is connected. -/
@[stacks 0BTW]
#check (AlgebraicGeometry.SchemeOverField.instConnectedSpacePerfectClosure :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [ConnectedSpace X.left],
    ConnectedSpace (FieldExtension.baseChange k (kᵖᵉʳᶠ) X.hom))

/- Lemma 58.14.2 (2): the canonical perfect-closure projection induces an isomorphism of
étale fundamental groups at every geometric point of the base change. -/
@[stacks 0BTW]
#check (AlgebraicGeometry.SchemeOverField.fundamentalGroupIsoPerfectClosure :
  ∀ {k : Type u} [Field k] (X : SchemeOverField k) [ConnectedSpace X.left]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω]
    (s : Spec (CommRingCat.of Ω) ⟶ FieldExtension.baseChange k (kᵖᵉʳᶠ) X.hom),
    IsHomeomorph (Scheme.Hom.fundamentalGroupMap
      (FieldExtension.toSource k (kᵖᵉʳᶠ) X.hom) s))
