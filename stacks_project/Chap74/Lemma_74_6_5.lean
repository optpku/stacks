/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Lemma_66_31_3_LocallyProjective
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsLocallyProjective

/-- Lemma 74.6.5: a quasi-coherent module `ℱ` on an algebraic space `X` over a
scheme `S` is locally projective if its pullbacks along an fpqc covering family
are locally projective. -/
@[stacks 060Y]
theorem of_fpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : FpqcCovering family)
    (hpullback : ∀ i, IsLocallyProjective ((Modules.pullback (family i).hom).obj ℱ)) :
    IsLocallyProjective ℱ := sorry

end IsLocallyProjective
end AlgebraicGeometry.AlgebraicSpace.Modules
