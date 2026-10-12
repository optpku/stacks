/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.DeligneSystem.Restriction
public import ReasLib.CategoryTheory.Pro.RepresentedHom

/-!
# Extension-by-zero restriction

This module constructs the canonical natural transformation from restriction followed by
extension by zero to extension by zero along an open immersion.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open DerivedCategory.Bounded.CohomologyIn
open scoped DerivedCategory.CohomologyIn

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem

variable {U X Z : Scheme.{u}}

/-- The extension-by-zero Hom comparison, promoted from its bijective function to an
equivalence. -/
noncomputable def extensionByZeroHomEquiv (j : X ⟶ Z)
    [IsNoetherian X] [IsNoetherian Z] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent Z.ringCatSheaf]) :
    ((extensionByZero j).obj K ⟶ Pro.yoneda.obj L) ≃ (K ⟶ (restriction j).obj L) :=
  Equiv.ofBijective (extensionByZeroHomMap j K L)
    (extensionByZeroHomMap_bijective j K L)

/-- The forward map of `extensionByZeroHomEquiv` is the canonical Hom comparison. -/
theorem extensionByZeroHomEquiv_apply (j : X ⟶ Z)
    [IsNoetherian X] [IsNoetherian Z] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent Z.ringCatSheaf])
    (a : (extensionByZero j).obj K ⟶ Pro.yoneda.obj L) :
    extensionByZeroHomEquiv j K L a = extensionByZeroHomMap j K L a := sorry

/-- Restriction on represented Hom types, transported through the extension-by-zero Hom
equivalences and the comparison for iterated restriction. -/
noncomputable def extensionByZeroRestrictionHomApp (i : U ⟶ X) (j : X ⟶ Z)
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Z]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent Z.ringCatSheaf]) :
    (Pro.representedHom (extensionByZero j)).obj (Opposite.op K, L) ⟶
      (Pro.representedHom (extensionByZero (i ≫ j))).obj
        (Opposite.op ((restriction i).obj K), L) :=
  ↾fun a ↦
    (extensionByZeroHomEquiv (i ≫ j) ((restriction i).obj K) L).symm
      ((restriction i).map (extensionByZeroHomEquiv j K L a) ≫
        (restrictionCompIso i j).hom.app L)

/-- The represented-Hom restriction component is the transport of ordinary restriction
through the two extension-by-zero Hom equivalences. -/
theorem extensionByZeroRestrictionHomApp_apply (i : U ⟶ X) (j : X ⟶ Z)
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Z]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])
    (L : Dᵇ[SheafOfModules.isCoherent Z.ringCatSheaf])
    (a : (Pro.representedHom (extensionByZero j)).obj (Opposite.op K, L)) :
    extensionByZeroRestrictionHomApp i j K L a =
      (extensionByZeroHomEquiv (i ≫ j) ((restriction i).obj K) L).symm
        ((restriction i).map (extensionByZeroHomEquiv j K L a) ≫
          (restrictionCompIso i j).hom.app L) := sorry

/-- The represented-Hom restriction components are natural in the bounded coherent source
and target variables. -/
theorem extensionByZeroRestrictionHomApp_naturality (i : U ⟶ X) (j : X ⟶ Z)
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Z]
    [IsOpenImmersion i] [IsOpenImmersion j]
    {p q :
      (Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])ᵒᵖ ×
        Dᵇ[SheafOfModules.isCoherent Z.ringCatSheaf]}
    (a : p ⟶ q) :
    (Pro.representedHom (extensionByZero j)).map a ≫
        extensionByZeroRestrictionHomApp i j q.1.unop q.2 =
      extensionByZeroRestrictionHomApp i j p.1.unop p.2 ≫
        ((restriction i).op.prod (𝟭 _) ⋙
          Pro.representedHom (extensionByZero (i ≫ j))).map a := sorry

/-- The represented-Hom transformation induced by restriction before extension by zero. -/
noncomputable def extensionByZeroRestrictionHom (i : U ⟶ X) (j : X ⟶ Z)
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Z]
    [IsOpenImmersion i] [IsOpenImmersion j] :
    Pro.representedHom (extensionByZero j) ⟶
      (restriction i).op.prod (𝟭 _) ⋙
        Pro.representedHom (extensionByZero (i ≫ j)) where
  app p := extensionByZeroRestrictionHomApp i j p.1.unop p.2
  naturality _ _ a := extensionByZeroRestrictionHomApp_naturality i j a

/-- The component of `extensionByZeroRestrictionHom` is the explicit transported Hom map. -/
theorem extensionByZeroRestrictionHom_app (i : U ⟶ X) (j : X ⟶ Z)
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Z]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (p :
      (Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf])ᵒᵖ ×
        Dᵇ[SheafOfModules.isCoherent Z.ringCatSheaf]) :
    (extensionByZeroRestrictionHom i j).app p =
      extensionByZeroRestrictionHomApp i j p.1.unop p.2 := sorry

/-- The canonical natural transformation from restricted-then-extended-by-zero to
extension by zero, functorial in the bounded coherent object. -/
noncomputable def extensionByZeroRestriction (i : U ⟶ X) (j : X ⟶ Z)
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Z]
    [IsOpenImmersion i] [IsOpenImmersion j] :
    restriction i ⋙ extensionByZero (i ≫ j) ⟶ extensionByZero j where
  app := ((Pro.representedHomNatTransEquiv
    (restriction i ⋙ extensionByZero (i ≫ j)) (extensionByZero j)).symm
      (extensionByZeroRestrictionHom i j ≫
        (Pro.representedHomPrecompIso
          (restriction i) (extensionByZero (i ≫ j))).inv)).app
  naturality := ((Pro.representedHomNatTransEquiv
    (restriction i ⋙ extensionByZero (i ≫ j)) (extensionByZero j)).symm
      (extensionByZeroRestrictionHom i j ≫
        (Pro.representedHomPrecompIso
          (restriction i) (extensionByZero (i ≫ j))).inv)).naturality

/-- The component of `extensionByZeroRestriction` is the canonical map selected by
its represented-Hom restriction transformation. -/
theorem extensionByZeroRestriction_app (i : U ⟶ X) (j : X ⟶ Z)
    [IsNoetherian U] [IsNoetherian X] [IsNoetherian Z]
    [IsOpenImmersion i] [IsOpenImmersion j]
    (K : Dᵇ[SheafOfModules.isCoherent X.ringCatSheaf]) :
    (extensionByZeroRestriction i j).app K =
      ((Pro.representedHomNatTransEquiv
        (restriction i ⋙ extensionByZero (i ≫ j)) (extensionByZero j)).symm
          (extensionByZeroRestrictionHom i j ≫
            (Pro.representedHomPrecompIso
              (restriction i) (extensionByZero (i ≫ j))).inv)).app K := sorry

end AlgebraicGeometry.Scheme.ModuleDerived.DeligneSystem
