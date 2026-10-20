module

public import ReasLib.AlgebraicGeometry.Scheme.CoherentFormalModule.Category
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Cofinal

/-!
# Changing the ideal of coherent formal modules

This file compares coherent formal-module categories on a Noetherian scheme for ideal sheaves
whose positive powers are mutually contained.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.CoherentFormalModules

/-- On a Noetherian scheme, ideal sheaves with mutually contained positive powers define
equivalent coherent formal-module categories. -/
theorem nonemptyEquivalence_of_pow_le {X : Scheme.{u}} [IsNoetherian X]
    (I J : X.IdealSheafData)
    (c d : ℕ) (hc : 0 < c) (hd : 0 < d) (hIJ : I ^ c ≤ J) (hJI : J ^ d ≤ I) :
    Nonempty (Scheme.CoherentFormalModules X I ≌ Scheme.CoherentFormalModules X J) := sorry

/-- On a Noetherian scheme, ideal sheaves with the same support define equivalent coherent
formal-module categories. -/
theorem nonemptyEquivalence_of_support_eq {X : Scheme.{u}} [IsNoetherian X]
    (I J : X.IdealSheafData) (h : I.support = J.support) :
    Nonempty (Scheme.CoherentFormalModules X I ≌ Scheme.CoherentFormalModules X J) := sorry

end AlgebraicGeometry.Scheme.CoherentFormalModules
