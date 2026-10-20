module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.WeaklyAssociatedPoints.ExactSequence
import StacksCheckRecall

/-!
# Lemma 71.2.4

In a short exact sequence of quasi-coherent modules on an algebraic space, the
weakly associated locus of the middle term is contained in the union of the
outer loci, and the left locus is contained in the middle locus.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 71.2.4 (1): in a short exact sequence of quasi-coherent modules on an algebraic
space, every weakly associated point of the middle term belongs to one of the outer loci. -/
@[stacks 0CTZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss_middle_subset_union_of_shortExact_of_isQuasicoherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {C : ShortComplex X.Modules}
      [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
      (hC : C.ShortExact), C.X₂.weakAss ⊆ C.X₁.weakAss ∪ C.X₃.weakAss)

/- Lemma 71.2.4 (2): in a short exact sequence of quasi-coherent modules on an algebraic
space, every weakly associated point of the left term belongs to the middle locus. -/
@[stacks 0CTZ] #check
  (AlgebraicGeometry.AlgebraicSpace.Modules.weakAss_left_subset_of_shortExact_of_isQuasicoherent :
    ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {C : ShortComplex X.Modules}
      [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
      (hC : C.ShortExact), C.X₁.weakAss ⊆ C.X₂.weakAss)
