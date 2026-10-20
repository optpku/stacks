module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Derived.ExtensionByZero

/-!
# Compatibility checks for derived étale extension by zero
-/

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Etale

#check etaleModuleSheaf_preadditive
#check etaleDerivedRestriction
#check etaleDerivedRestriction_def
#check etaleDerivedExtensionByZero
#check etaleDerivedExtensionByZero_def
#check etaleDerivedExtensionByZeroAdjunction
#check etaleDerivedExtensionByZeroRestrict
#check etaleDerivedExtensionByZeroRestrict_obj
#check etaleRestriction_comp
#check etaleRestrictionSheaf_comp
#check moduleExtensionByZero_comp
#check etaleDerivedRestriction_comp
#check etaleDerivedExtensionByZero_comp

end AlgebraicGeometry.Scheme.Etale
