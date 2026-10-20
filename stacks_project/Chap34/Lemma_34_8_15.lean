module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.Sheaf
import StacksCheckRecall

open CategoryTheory

universe u v

/- Lemma 34.8.15 (1): a presheaf on `(Sch/S)_{ph}` is a sheaf if and only if it
satisfies the Zariski sheaf condition and the proper-surjective equalizer condition. -/
@[stacks 0DBQ] #check
  (AlgebraicGeometry.Scheme.Ph.Sheaf.iffZariskiAndEqualizer :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (F : (CategoryTheory.Over S)ᵒᵖ ⥤ Type v),
      CategoryTheory.Presheaf.IsSheaf (AlgebraicGeometry.Scheme.bigPhSite S) F ↔
        CategoryTheory.Presheaf.IsSheaf
            (AlgebraicGeometry.Scheme.zariskiTopology.over S) F ∧
          AlgebraicGeometry.Scheme.Ph.Equalizer.IsProperSurjective F)

/- Lemma 34.8.15 (2): assuming the Zariski sheaf condition, the
proper-surjective equalizer condition can be checked on affine targets. -/
@[stacks 0DBQ] #check
  (AlgebraicGeometry.Scheme.Ph.Equalizer.iffAffine :
    ∀ {S : AlgebraicGeometry.Scheme.{u}}
      (F : (CategoryTheory.Over S)ᵒᵖ ⥤ Type v),
      CategoryTheory.Presheaf.IsSheaf
          (AlgebraicGeometry.Scheme.zariskiTopology.over S) F →
        (AlgebraicGeometry.Scheme.Ph.Equalizer.IsProperSurjective F ↔
          AlgebraicGeometry.Scheme.Ph.Equalizer.IsAffineProperSurjective F))
