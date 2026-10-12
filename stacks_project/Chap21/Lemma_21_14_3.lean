/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Sheaf.GlobalSections.Acyclic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Acyclic
public import ReasLib.AlgebraicGeometry.RingedSite.Module.Pushforward.Acyclic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.14.3

The four acyclicity assertions are exposed through the bounded-below
`Functor.RightAcyclic.Bounded` API.  The arbitrary-presheaf clause is owned at
the site-generic abelian-sheaf layer; the remaining declarations are thin
ringed-site module bridges.
-/

/- Lemma 21.14.3 (1) (0731): a totally acyclic module sheaf is right acyclic for sections
over every object of the site. -/
@[stacks 0731 "(1)"]
#check @RingedSite.Hom.ModuleSections.rightAcyclicForObject

/- Lemma 21.14.3 (2) (0731): a totally acyclic abelian sheaf is right acyclic for sections
over every type-valued presheaf. -/
@[stacks 0731 "(2)"]
#check @CategoryTheory.Sheaf.IsTotallyAcyclic.rightAcyclicForPresheaf

-- Localization at a sheaf of sets gives the corresponding module-valued specialization.
#check @RingedSite.Localization.AtSheaf.ModuleSections.rightAcyclic

/- Lemma 21.14.3 (3) (0731): a totally acyclic module sheaf is right acyclic for global
sections. -/
@[stacks 0731 "(3)"]
#check @RingedSite.Hom.ModuleSections.rightAcyclicForGlobalSections

/- Lemma 21.14.3 (4) (0731): a totally acyclic module sheaf is right acyclic for direct
image along a morphism of ringed sites. -/
@[stacks 0731 "(4)"]
#check @RingedSite.Hom.modulePushforward.rightAcyclic_of_isTotallyAcyclic

end
