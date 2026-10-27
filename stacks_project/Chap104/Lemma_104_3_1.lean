/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Sites.DerivedLowerShriek
import StacksCheckRecall

/-!
# Lemma 104.3.1

On an algebraic stack, abelian and module lower shriek along the lisse-étale
and flat-fppf inclusions admit unbounded left derived functors, left adjoint
to exact derived inverse image, with `g⁻¹ Lg_! = id` and `g^* Lg_! = id`.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicStack
open AlgebraicGeometry.GroupoidsOver CategoryTheory
open RingedSite.Cocontinuous

noncomputable section

universe u z

namespace AlgebraicGeometry.AlgebraicStack

variable {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X]
variable [UnivLE.{u + 1, z}]

/- Lemma 104.3.1 (1): the functor g_! on abelian sheaves of the lisse-étale
site has an unbounded left derived functor
Lg_! : D(X_lisse,étale) ⥤ D(X_étale) which is left adjoint to g⁻¹ and
satisfies g⁻¹ Lg_! = id. -/
@[stacks 07AS]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriekDerived X :
  DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}) ⥤
    DerivedCategory (Sheaf (X.etaleTopology) AddCommGrpCat.{z}))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriekDerived.adjunction X :
  lisseEtaleAbelianLowerShriekDerived.{u, z} X ⊣ siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) (X.etaleTopology) (lisseEtaleInclusion X))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriekDerived_unit_app_isIso X :
  ∀ F : DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z}),
    IsIso ((lisseEtaleAbelianLowerShriekDerived.adjunction X).unit.app F))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleAbelianLowerShriekDerived_comp_inverseImage X :
  lisseEtaleAbelianLowerShriekDerived X ⋙ siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (lisseEtaleTopology X) (X.etaleTopology) (lisseEtaleInclusion X) ≅ 𝟭 (DerivedCategory (Sheaf (lisseEtaleTopology X) AddCommGrpCat.{z})))

/- Lemma 104.3.1 (2): the functor g_! on modules of the lisse-étale site has an
unbounded left derived functor
Lg_! : D(𝒪_{X_lisse,étale}) ⥤ D(X_étale, 𝒪_X) which is left adjoint to g^*
and satisfies g^* Lg_! = id. -/
@[stacks 07AS]
#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusionDerivedLowerShriek X :
  RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X) ⥤
    RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (X.etaleTopology) (etaleStructureSheaf X)))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleInclusionDerivedLowerShriek.adjunction X :
  lisseEtaleInclusionDerivedLowerShriek.{u, z} X ⊣ lisseEtaleInclusionDerivedInverseImage X)

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriekDerived_unit_app_isIso X :
  ∀ F : RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X),
    IsIso ((lisseEtaleInclusionDerivedLowerShriek.adjunction X).unit.app F))

#check (AlgebraicGeometry.AlgebraicStack.lisseEtaleModuleLowerShriekDerived_comp_inverseImage X :
  lisseEtaleInclusionDerivedLowerShriek X ⋙ lisseEtaleInclusionDerivedInverseImage X ≅ 𝟭 (RingedSite.Hom.ModuleDerived.{z} (lisseEtaleRingedSite X)))

/- Lemma 104.3.1 (3): the functor g_! on abelian sheaves of the flat-fppf site
has an unbounded left derived functor
Lg_! : D(X_flat,fppf) ⥤ D(X_fppf) which is left adjoint to g⁻¹ and
satisfies g⁻¹ Lg_! = id. -/
@[stacks 07AS]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriekDerived X :
  DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}) ⥤
    DerivedCategory (Sheaf (inheritedFppfTopology X) AddCommGrpCat.{z}))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriekDerived.adjunction X :
  flatFppfAbelianLowerShriekDerived.{u, z} X ⊣ siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriekDerived_unit_app_isIso X :
  ∀ F : DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z}),
    IsIso ((flatFppfAbelianLowerShriekDerived.adjunction X).unit.app F))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfAbelianLowerShriekDerived_comp_inverseImage X :
  flatFppfAbelianLowerShriekDerived X ⋙ siteAbelianInverseImageDerived.{u + 1, u, u + 1, u, z}
      (flatFppfTopology X) (inheritedFppfTopology X) (flatFppfInclusion X) ≅ 𝟭 (DerivedCategory (Sheaf (flatFppfTopology X) AddCommGrpCat.{z})))

/- Lemma 104.3.1 (4): the functor g_! on modules of the flat-fppf site has an
unbounded left derived functor
Lg_! : D(𝒪_{X_flat,fppf}) ⥤ D(𝒪_X) which is left adjoint to g^* and
satisfies g^* Lg_! = id. -/
@[stacks 07AS]
#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusionDerivedLowerShriek X :
  RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X) ⥤
    RingedSite.Hom.ModuleDerived.{z}
      (RingedSite.ofRingSheaf (inheritedFppfTopology X) (structureSheaf X)))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfInclusionDerivedLowerShriek.adjunction X :
  flatFppfInclusionDerivedLowerShriek.{u, z} X ⊣ flatFppfInclusionDerivedInverseImage X)

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriekDerived_unit_app_isIso X :
  ∀ F : RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X),
    IsIso ((flatFppfInclusionDerivedLowerShriek.adjunction X).unit.app F))

#check (AlgebraicGeometry.AlgebraicStack.flatFppfModuleLowerShriekDerived_comp_inverseImage X :
  flatFppfInclusionDerivedLowerShriek X ⋙ flatFppfInclusionDerivedInverseImage X ≅ 𝟭 (RingedSite.Hom.ModuleDerived.{z} (flatFppfRingedSite X)))

/- Warning: it is not a priori clear that Lg_! on modules agrees with Lg_! on
abelian sheaves; the only canonical comparison is the derived underlying mate
of Remark 21.37.3, which is not asserted to be an isomorphism. -/

end AlgebraicGeometry.AlgebraicStack
