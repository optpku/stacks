module

import StacksCheckRecall
public import stacks_project.Chap42.Definition_42_46_3_DerivedChern

/- Definition 42.46.3 (1): the Chern classes of a derived module are defined when an envelope
makes its derived pullback admit a locally bounded, termwise finite locally free representative. -/
@[stacks 0F9E] #check AlgebraicGeometry.ChernClass.Derived.IsDefined

/- Definition 42.46.3 (2): for a perfect derived module with defined Chern classes, `c(E)` is
the integral total Chern-class family characterized by restriction to every eligible envelope. -/
@[stacks 0F9E] #check AlgebraicGeometry.ChernClass.Derived.totalClass

/- Definition 42.46.3 (3): for a perfect derived module with defined Chern classes, `ch(E)` is
the rational Chern-character family characterized by restriction to every eligible envelope. -/
@[stacks 0F9E] #check AlgebraicGeometry.ChernClass.Derived.character

/- Definition 42.46.3 (4): for a perfect derived module with defined Chern classes, `P_p(E)` is
the degree-`p` Newton class in the selected integral Newton-class family. -/
@[stacks 0F9E] #check AlgebraicGeometry.ChernClass.Derived.newtonClass
