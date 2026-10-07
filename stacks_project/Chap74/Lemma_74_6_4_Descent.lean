module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering

/-!
# Descent of finite locally free modules on algebraic spaces

Finite local freeness for quasi-coherent modules on algebraic spaces descends along
fpqc covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Modules.IsFiniteLocallyFree

/-- A quasi-coherent module on an algebraic space whose pullbacks along an fpqc covering
family are finite locally free is itself finite locally free. -/
theorem of_fpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (ℱ : X.Modules) [ℱ.IsQuasicoherent]
    (family : ι → Over X) (hfamily : AlgebraicSpace.FpqcCovering family)
    (hpullback : ∀ i : ι,
      ((AlgebraicSpace.Modules.pullback (family i).hom).obj ℱ).IsFiniteLocallyFree) :
    ℱ.IsFiniteLocallyFree := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules.IsFiniteLocallyFree
