/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.LocalCompleteIntersection
import StacksCheckRecall

/-!
# Local complete intersection curves

There is an open substack 𝒞urves^{lci} ⊂ 𝒞urves classifying local complete
intersection families of curves, equivalently proper local complete intersection
schemes of dimension at most one over a field.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace
namespace Spaces
namespace Curves

/- Lemma 109.13.1 (1): given a family of curves `X ⟶ S`, the classifying
morphism `S ⟶ 𝒞urves` factors through `𝒞urves^{lci}` if and only if `X ⟶ S`
is a local complete intersection morphism if and only if `X ⟶ S` is syntomic. -/
@[stacks 0DZV] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_lci_tfae :
    ∀ {S : Scheme.{u}} (P : Obj S),
    List.TFAE [lci S P, AlgebraicSpace.IsLocalCompleteIntersection (hom P),
      AlgebraicSpace.Syntomic (hom P)])

/- Lemma 109.13.1 (2): given a scheme `X` proper over a field `k` with
dimension at most one, the classifying morphism `Spec k ⟶ 𝒞urves` factors
through `𝒞urves^{lci}` if and only if `X` is a local complete intersection
over `k`. -/
@[stacks 0DZV] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.classifying_factorsThrough_lci_iff_scheme :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
      (hdim : topologicalKrullDim X.left ≤ 1),
    lci (Spec (CommRingCat.of k)) (mkOfSchemeOverField X hdim) ↔
      IsLocalCompleteIntersectionOver k X.hom)

/- The open-substack assertion is represented on every family's base by an
open whose universal property holds under arbitrary scheme base change. -/
#check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.exists_lci_open :
    ∀ {S : Scheme.{u}} (P : Obj S),
      ∃ U : (base P).left.Opens, ∀ T : Over (base P).left,
        AlgebraicSpace.IsLocalCompleteIntersection
            (pullbackAlongScheme.snd (hom P)
              (ofOverHomMk (σK := T.hom ≫ (base P).hom)
                (σL := (base P).hom) T.hom rfl)) ↔
          Set.range T.hom ⊆ U)

end Curves
end Spaces
end AlgebraicGeometry.AlgebraicSpace
