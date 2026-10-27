/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Module.Associated
public import ReasLib.AlgebraicGeometry.GroupoidsOver.Etale.Module.Restriction

/-!
# Atlas restriction of modules on a quotient stack

For a groupoid in algebraic spaces `(U, R, s, t, c)` with quotient stack
`𝒳 = [U / R]` and atlas `x : 𝒮_U ⟶ 𝒳`, restriction of an arbitrary
`𝒪_𝒳`-module `M` to the small étale site of `U` is
`x^* M |_{U_étale}`. The induced map on Hom-spaces is
`φ ↦ x^* φ |_{U_étale}`.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.GroupoidAlgebraicSpace
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

variable {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- Restriction of an `𝒪_[U / R]`-module to the small étale site of `U`, as
`x^* M |_{U_étale}`. -/
def atlasRestrictModules (M : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G))) :
    SheafOfModules.{u} (AlgebraicSpace.structureSheaf G.U.left) :=
  (restrictModules (Bicategory.Equivalence.id G.U.left.toGroupoids)).obj
    ((etaleModuleInverseImage (SmallQuotient.atlas G)).obj ((toEtaleModules (SmallQuotient.quotientStack G)).obj M))

/-- `atlasRestrictModules G M` is restriction of the étale inverse image of `M` along
the atlas. -/
theorem atlasRestrictModules_eq
    (M : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G))) :
    atlasRestrictModules G M =
      (restrictModules (Bicategory.Equivalence.id G.U.left.toGroupoids)).obj
        ((etaleModuleInverseImage (SmallQuotient.atlas G)).obj
          ((toEtaleModules (SmallQuotient.quotientStack G)).obj M)) :=
  rfl

/-- The map `Hom_{𝒪_𝒳}(ℱ, ℋ) → Hom_{𝒪_U}(x^* ℱ |_{U_étale}, x^* ℋ |_{U_étale})`
sending `φ` to `x^* φ |_{U_étale}`. -/
def atlasRestrictHom (F : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G)))
    (H : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G))) :
    (F ⟶ H) →
      (atlasRestrictModules G F ⟶ atlasRestrictModules G H) :=
  fun ψ ↦
    (restrictModules (Bicategory.Equivalence.id G.U.left.toGroupoids)).map
      ((etaleModuleInverseImage (SmallQuotient.atlas G)).map
        ((toEtaleModules (SmallQuotient.quotientStack G)).map ψ))

/-- `atlasRestrictHom` is restriction of the étale inverse image of `ψ` along the
atlas. -/
theorem atlasRestrictHom_app (F : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G)))
    (H : RingedSite.ModuleCat.{u} (ringedSite (SmallQuotient.quotientStack G)))
    (ψ : F ⟶ H) :
    atlasRestrictHom G F H ψ =
      (restrictModules (Bicategory.Equivalence.id G.U.left.toGroupoids)).map
        ((etaleModuleInverseImage (SmallQuotient.atlas G)).map
          ((toEtaleModules (SmallQuotient.quotientStack G)).map ψ)) :=
  rfl

end AlgebraicGeometry.GroupoidsOver
