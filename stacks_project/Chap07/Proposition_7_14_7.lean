module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.MorphismOfSites.Criteria

@[expose] public section

/- Proposition 7.14.7 (00X6): the reusable criterion packages a continuous functor preserving
terminal objects and pullbacks as a morphism of sites. -/
@[stacks 00X6] #check @CategoryTheory.IsMorphismOfSites.of_preservesTerminal_and_pullbacks

/- The explicit-terminal-object form is useful when a terminal object is part of the source
data rather than an ambient typeclass. -/
#check @CategoryTheory.IsMorphismOfSites.of_terminal_and_pullbacks

/- Representable flatness is the underlying non-topological conclusion of the same criterion. -/
#check @CategoryTheory.RepresentablyFlat.of_terminal_and_pullbacks

/- The terminal-object bridge is available independently for finite-limit arguments. -/
#check @CategoryTheory.Functor.preservesTerminal_of_isTerminal
