module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Representability

@[expose] public section

open AlgebraicGeometry

/- Example 26.15.2 (1): the Type-valued functor of global sections. -/
@[stacks 01JH] #check Scheme.GlobalSections.functor

/- Example 26.15.2 (2): global sections are represented by the integral
affine line. -/
@[stacks 01JH] #check Scheme.GlobalSections.representingIso
#check Scheme.GlobalSections.affineLine
#check Scheme.GlobalSections.homEquiv

/- Example 26.15.2 (3): the representing object carries the universal
coordinate section. -/
@[stacks 01JH] #check Scheme.GlobalSections.universalSection
#check Scheme.GlobalSections.homEquiv_apply

/- Example 26.15.2 (4): the universal section is the polynomial
coordinate. -/
@[stacks 01JH] #check Scheme.GlobalSections.universalSection_eq_coordinate
