module

import StacksCheckRecall
public import stacks_project.Chap42.Definition_42_50_3_RationalBivariant
public import stacks_project.Chap42.Definition_42_50_3_LocalizedClasses

@[expose] public section

namespace AlgebraicGeometry.LocalizedChern

/- Definition 42.50.3 (1): the localized Newton class in the vanishing case. -/
@[stacks 0FB5] #check newtonClass

/- Definition 42.50.3 (2): the completed localized Chern character with components
`Pₚ(Z ⟶ X, E) / p!`. -/
@[stacks 0FB5] #check character

/- Definition 42.50.3 (3): the localized `p`th Chern class in the rank-bound case. -/
@[stacks 0FB5] #check chernClass

end AlgebraicGeometry.LocalizedChern
