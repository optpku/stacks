module

public import ReasLib.Algebra.Homology.DerivedCategory.ProjectiveAmplitude.Ext
import StacksCheckRecall

/-!
# Lemma 15.77.5

@stack 0G97
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory.TStructure

noncomputable section

universe u

namespace CategoryTheory

variable {R : Type u} [Ring R]
variable (K : DerivedCategory.Minus (ModuleCat R)) (a : ℤ)
variable (hExt : (DerivedCategory.Ext.addCommGrpFunctor K.obj (-a)).PreservesMonomorphisms)

/- Lemma 15.77.5: preservation of monomorphisms by `Ext^{-a}_R(K, -)` gives projective amplitude
for `τ≥ a + 1` and the unique compatible decomposition `K ≅ τ≤ a K ⊞ τ≥ a + 1 K`. -/
@[stacks 0G97 "Ext mono-preservation and truncation splitting"]
#check
  (DerivedCategory.ProjectiveAmplitude.existsUnique_truncationBiprod_of_ext_preservesMonomorphisms
      K a hExt :
    ∃ b : ℤ,
      HasProjectiveAmplitudeIn ((t.truncGE (a + 1)).obj K.obj) (a + 1) b ∧
        ∃! e : K.obj ≅ (t.truncLE a).obj K.obj ⊞ (t.truncGE (a + 1)).obj K.obj,
          ((t.truncLEι a).app K.obj) ≫ e.hom = biprod.inl ∧
            e.hom ≫ biprod.snd = ((t.truncGEπ (a + 1)).app K.obj))

#check @DerivedCategory.Ext.addCommGrpFunctor

end CategoryTheory
