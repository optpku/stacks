module

public import Mathlib.Algebra.Category.Grp.Abelian
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Derived
public import ReasLib.AlgebraicGeometry.RingedSite.Module.GlobalSections.Naturality
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Exact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Tactic.CrossRefAttribute

/-!
# Naturality of derived global sections on ringed sites

This module lifts the underived direct-image comparison for module global sections to the
homotopy-to-derived functors used to define unbounded derived global sections.
-/

@[expose] public section

open CategoryTheory
open ComplexShape

noncomputable section

universe z uX vX uY vY w

namespace RingedSite.Hom

/-- The exact derived restriction of scalars on global-sections modules. -/
@[stacks 0D6H "derived restriction of global-sections scalars"]
noncomputable abbrev globalSectionsRestrictionDerived.{z₁, u₁, v₁, u₂, v₂, w₁}
    {X : RingedSite.{u₁, v₁, w₁}} {Y : RingedSite.{u₂, v₂, w₁}}
    [UnivLE.{u₁, w₁}] [UnivLE.{u₂, w₁}]
    [UnivLE.{max u₁ v₁, w₁}] [UnivLE.{max u₂ v₂, w₁}]
    [UnivLE.{max u₂ v₁, w₁}]
    (f : Hom X Y)
    [UnivLE.{max u₁ v₁, z₁}] [UnivLE.{max u₂ v₂, z₁}] :
    ModuleSections.Derived.{z₁} X ⥤ ModuleSections.Derived.{z₁} Y :=
  CategoryTheory.Functor.mapDerivedCategory
    (globalSectionsRestriction.{z₁, u₁, v₁, u₂, v₂, w₁} (X := X) (Y := Y) f)

namespace ModuleSections

/-- The natural transformation from homotopy-level global sections on `X` to global sections
after homotopy-level direct image along a morphism of ringed sites. -/
@[stacks 0D6H "derived global-sections naturality"]
noncomputable def derivedPushforwardNat
    {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}} (f : Hom X Y)
    [UnivLE.{uX, z}] [UnivLE.{uY, z}]
    [HasWeakSheafify X.siteTopology AddCommGrpCat.{z}]
    [HasWeakSheafify Y.siteTopology AddCommGrpCat.{z}] :
    moduleGlobalSectionsToDerived.{z} X ⟶
      f.modulePushforward.{z}.mapHomotopyCategory (up ℤ) ⋙
        moduleGlobalSectionsToDerived.{z} Y :=
  -- Local instance justification (proof-local temporary data): homotopy-category lift consumes the canonical additivity theorem for global sections on `X`.
  letI : (moduleGlobalSectionsAdditiveFunctor.{z} X).Additive :=
    moduleGlobalSectionsAdditiveFunctor_additive.{z, uX, vX, w} X
  -- Local instance justification (proof-local temporary data): comparison and associator consume the canonical additivity theorem for global sections on `Y`.
  letI : (moduleGlobalSectionsAdditiveFunctor.{z} Y).Additive :=
    moduleGlobalSectionsAdditiveFunctor_additive.{z, uY, vY, w} Y
  Functor.whiskerRight
      (NatTrans.mapHomotopyCategory
        (pushforwardNat.{z} f) (up ℤ))
      DerivedCategory.Qh ≫
    Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso
        (Iso.refl
          (f.modulePushforward.{z} ⋙ moduleGlobalSectionsAdditiveFunctor.{z} Y))
        (up ℤ)).inv
      DerivedCategory.Qh ≫
    (Functor.associator
      (f.modulePushforward.{z}.mapHomotopyCategory (up ℤ))
      ((moduleGlobalSectionsAdditiveFunctor.{z} Y).mapHomotopyCategory (up ℤ))
      DerivedCategory.Qh).hom

end ModuleSections

end RingedSite.Hom

-- The components are inherited canonical whiskerings and associators; deferred axioms, if any,
-- come from the upstream functors rather than from a chosen natural-transformation payload.
