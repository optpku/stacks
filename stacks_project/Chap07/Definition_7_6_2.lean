module

public import stacks_project.Chap07.Definition_7_6_2_Site
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- Definition 7.6.2: a site is a category C together with a set Cov(C) of
families of morphisms with fixed target {Uᵢ ⟶ U}_{i ∈ I}, called coverings of
C, such that (1) every isomorphism V ⟶ U is a singleton covering, (2) coverings
are stable under bind of covering families, and (3) pullbacks of covering
arrows along any V ⟶ U exist and the pulled-back family covers V. This is the
unbundled owner Precoverage.IsSite on an explicit precoverage. -/
@[stacks 00VH] #check @Precoverage.IsSite
