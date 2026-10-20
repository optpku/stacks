module

public import ReasLib.CategoryTheory.Fibered.Gerbe.Band
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 8.11.8

The chapter entry recalls the neutral Gerbe/Band owner.  The former Part16 module was a
construction-stage proof forest; its public mathematical surface is the canonical projection-level
abelianity class, the comparison predicate, and the global existence theorem exported by ReasLib.
-/

namespace CategoryTheory

/- Lemma 8.11.8 (0CJY): an abelian gerbe admits a global band. -/
@[stacks 0CJY]
#check @IsGerbe.existsBand

#check @Functor.IsFibered.InGroupoids.Automorphism.IsAbelian
#check @Functor.IsFibered.InGroupoids.Automorphism.IsAbelian.iff_sections
#check @Functor.IsFibered.InGroupoids.Band.Comparison
#check @Functor.IsFibered.InGroupoids.Band.Comparison.iso
#check @Functor.IsFibered.InGroupoids.Band.Comparison.naturality
#check @Functor.IsFibered.InGroupoids.Band.Comparison.IsCompatibleIso
#check @Functor.IsFibered.InGroupoids.Band.Comparison.existsUniqueCompatibleIso
#check @Functor.IsFibered.InGroupoids.Band.Comparison.compatibleIso
#check @Functor.IsFibered.InGroupoids.Band.Comparison.compatibleIso_spec
#check @Functor.IsFibered.InGroupoids.Band.Comparison.compatibleIso_unique
#check @Functor.IsFibered.InGroupoids.Band.Choice
#check @Functor.IsFibered.InGroupoids.Band.Choice.sheaf
#check @Functor.IsFibered.InGroupoids.Band.Choice.comparison
#check @Functor.IsFibered.InGroupoids.Band.Choice.ofComparison
#check @Functor.IsFibered.InGroupoids.Band.Choice.ofExists
#check @Functor.IsFibered.InGroupoids.Band.Choice.isBand
#check @Functor.IsFibered.InGroupoids.Band.Choice.comparisonIso
#check @Functor.IsFibered.InGroupoids.Band.Choice.comparisonIso_spec
#check @Functor.IsFibered.InGroupoids.Band.Choice.comparisonIso_unique
#check @Functor.IsFibered.InGroupoids.IsBand
#check @Functor.IsFibered.InGroupoids.IsBand.existsComparison
#check @Functor.IsFibered.InGroupoids.IsBand.comparison
#check @Functor.IsFibered.InGroupoids.IsBand.nonemptyIso
#check @Functor.IsFibered.InGroupoids.Automorphism.addComm.sheaf
#check @Functor.IsFibered.InGroupoids.Automorphism.addComm.sheaf.conjOfHom
#check @IsGerbe.existsBandComparison
#check @IsGerbe.bandChoice
#check @IsGerbe.bandChoice_spec

end CategoryTheory
