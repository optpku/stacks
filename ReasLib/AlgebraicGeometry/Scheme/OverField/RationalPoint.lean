/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FinitePresentation
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Implications
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RegularImmersion.Section
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFree.Rank

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.RationalPoint

/-- The underlying map of a rational point has singleton range. -/
theorem range_eq_singleton
    {k : Type u} [Field k] (X : SchemeOverField k)
    (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    Set.range x.left = {x.left (IsLocalRing.closedPoint k)} := sorry

/-- A rational-point section of a separated scheme over a field is a closed immersion. -/
theorem isClosedImmersion
    {k : Type u} [Field k] (X : SchemeOverField k) [IsSeparated X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) : IsClosedImmersion x.left := sorry

/-- A rational-point section of a smooth separated scheme is of finite presentation. -/
theorem finitePresentation
    {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom] [IsSeparated X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) : Scheme.Hom.FinitePresentation x.left := sorry

/-- A rational-point section of a smooth scheme is a Koszul-regular immersion. -/
theorem isKoszulRegularImmersion
    {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom]
    (x : 𝟙_ (SchemeOverField k) ⟶ X) : IsKoszulRegularImmersion x.left := sorry

/-- The conormal sheaf of a rational-point section in a smooth relative `d`-fold has rank
`d`. -/
theorem conormalSheafIsFiniteLocallyFreeOfRank
    {k : Type u} [Field k] (X : SchemeOverField k) (d : ℕ)
    [SmoothOfRelativeDimension d X.hom] (x : 𝟙_ (SchemeOverField k) ⟶ X) :
    SheafOfModules.IsFiniteLocallyFreeOfRank d (Scheme.Hom.conormalSheaf x.left) := sorry

end AlgebraicGeometry.SchemeOverField.RationalPoint

end
