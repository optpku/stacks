module

public import ReasLib.Algebra.Category.Grp.CharacterModule
public import ReasLib.Algebra.Category.ModuleCat.Descent.SplitEqualizer
public import ReasLib.CategoryTheory.Limits.Shapes.Opposites.SplitEqualizer

/-!
# Character-dual split coequalizer of module descent data

Character duality sends the explicit additive split equalizer attached to module descent data
to an explicit split coequalizer.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat.DescentData.SplitCoequalizer

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Applying additive character duality to the descent split equalizer gives a split
coequalizer on the duals of its upper, lower, and source maps. -/
noncomputable def splitting (D : ModuleCat.DescentData (algebraMap R S)) :
    CategoryTheory.IsSplitCoequalizer
      (CharacterModule.dualAddMap (SplitEqualizer.upper D))
      (CharacterModule.dualAddMap (SplitEqualizer.lower D))
      (CharacterModule.dualAddMap (SplitEqualizer.source D)) :=
  (SplitEqualizer.splitting D).op.map CharacterModule.addCommGrpFunctor

end ModuleCat.DescentData.SplitCoequalizer
