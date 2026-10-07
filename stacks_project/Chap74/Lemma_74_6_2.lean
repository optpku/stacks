module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Modules
namespace IsFinitePresentation

/-- Lemma 74.6.2: a quasi-coherent module `ℱ` on an algebraic space `X` over a
scheme `S` is of finite presentation if its pullbacks along an fpqc covering
family are of finite presentation. -/
@[stacks 060V]
theorem of_fpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : FpqcCovering family)
    (hpullback :
      ∀ i : ι, ((Modules.pullback (family i).hom).obj ℱ).IsFinitePresentation) :
    ℱ.IsFinitePresentation := sorry

end IsFinitePresentation
end AlgebraicGeometry.AlgebraicSpace.Modules
