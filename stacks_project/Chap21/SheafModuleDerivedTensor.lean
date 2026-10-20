module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Monoidal

@[expose] public section

namespace SheafModuleDerivedTensor

open CategoryTheory.MonoidalCategory

/- Textbook surface notation for the derived tensor product object `K ⊗^L L` in a derived
category of sheaves of modules on a site, when the derived tensor is realized by the canonical
monoidal tensor on the ambient derived category. -/
scoped notation:70 K:70 " ⊗^L " L:71 => K ⊗ L

end SheafModuleDerivedTensor
