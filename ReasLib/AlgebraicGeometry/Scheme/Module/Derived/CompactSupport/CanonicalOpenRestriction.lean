module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Restriction
public import ReasLib.CategoryTheory.Pro.RepresentedHom

/-!
# The specified pro-object map for restriction between open complements

The map is the fully faithful pro-realization of restriction on represented Hom.
It does not choose a morphism from an existence theorem or accept presentation
compatibility as an input.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section
universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem

variable {X U U' : Scheme.{u}}
variable (i : U' ⟶ U) (j : U ⟶ X)
variable [IsNoetherian X] [IsNoetherian U] [IsNoetherian U']
variable [IsOpenImmersion i] [IsOpenImmersion j]
variable (K : Dᵇ[SheafOfModules.isCoherent U.ringCatSheaf])

/-- The prescribed operation on Hom into every constant coherent pro-object:
restrict the corresponding bounded-coherent morphism and use the canonical
composition comparison of open pullbacks. -/
def openRestrictionHomAction (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (a : (extensionByZero j).obj K ⟶ Pro.yoneda.obj L) :
    (extensionByZero (i ≫ j)).obj ((restriction i).obj K) ⟶ Pro.yoneda.obj L :=
  (Equiv.ofBijective
    (extensionByZeroHomMap (i ≫ j) ((restriction i).obj K) L)
    (extensionByZeroHomMap_bijective (i ≫ j) ((restriction i).obj K) L)).symm
      ((restriction i).map (extensionByZeroHomMap j K L a) ≫
        (restrictionCompIso i j).hom.app L)

/-- The represented-Hom operation is natural in the constant target. -/
def openRestrictionRealization :
    ((Pro.inclusion Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]).obj
      ((extensionByZero j).obj K)).unop ⟶
    ((Pro.inclusion Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]).obj
      ((extensionByZero (i ≫ j)).obj ((restriction i).obj K))).unop where
  app L := TypeCat.ofHom fun x ↦
    Pro.homYonedaEquiv ((extensionByZero (i ≫ j)).obj ((restriction i).obj K)) L
      (openRestrictionHomAction i j K L
        ((Pro.homYonedaEquiv ((extensionByZero j).obj K) L).symm x))
  naturality := sorry

/-- The geometric extension-by-zero restriction is the pro-morphism whose
fully faithful realization is the specified restriction on represented Hom. -/
def canonicalOpenRestriction :
    (extensionByZero (i ≫ j)).obj ((restriction i).obj K) ⟶
      (extensionByZero j).obj K :=
  Pro.inclusion.fullyFaithful.preimage (openRestrictionRealization i j K).op

/-- The constructed morphism acts on represented Hom by the actual
restriction operation used in its definition. -/
theorem canonicalOpenRestriction_comp
    (L : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (a : (extensionByZero j).obj K ⟶ Pro.yoneda.obj L) :
    canonicalOpenRestriction i j K ≫ a = openRestrictionHomAction i j K L a := sorry

/-- The constructed pro-morphism satisfies the existing geometric
restriction specification, with the restricted complex taken literally. -/
theorem canonicalOpenRestriction_isRestriction :
    IsExtensionByZeroRestriction i j K ((restriction i).obj K) (Iso.refl _)
      (canonicalOpenRestriction i j K) := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem
