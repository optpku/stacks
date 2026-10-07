module

public import ReasLib.Algebra.Category.ModuleCat.Descent.BaseExtension

@[expose] public section

universe u

open CategoryTheory

/- This source-side compatibility bridge preserves the complete type of base extension for
existing chapter imports. -/
#check (ModuleCat.baseExtension :
  ∀ {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S),
    ModuleCat.{u} R ⥤ ModuleCat.DescentData f)
