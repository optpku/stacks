/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.CategoryTheory.Subobject.Limits
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import stacks_project.Chap65.Lemma_65_12_4_Immersion
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject

/-!
# Kernel ideal sheaves of morphisms of algebraic spaces

The associated ideal sheaf of a morphism `i : Z ⟶ X` of algebraic spaces is the
kernel of the canonical map `𝒪_X ⟶ i_* 𝒪_Z` of `𝒪_X`-modules on the small
étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Hom

/-- The canonical `𝒪_X`-module map `𝒪_X ⟶ i_* 𝒪_Z` associated to a morphism of
algebraic spaces. -/
noncomputable def idealSheafMap {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) :
    SheafOfModules.unit (structureSheaf X) ⟶
      (SheafOfModules.pushforward
          (SheafOfModules.ChangeOfRings.homOverId (structureSheafMap i))).obj
        (SheafOfModules.unit ((ringPushforward i).obj (structureSheaf Z))) :=
  SheafOfModules.unitToPushforwardObjUnit
    (SheafOfModules.ChangeOfRings.homOverId (structureSheafMap i))

/-- The kernel of `𝒪_X ⟶ i_* 𝒪_Z`, as an ideal subobject of `𝒪_X`. -/
noncomputable abbrev idealSheafSubobject {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) : IdealSubobject X :=
  kernelSubobject (idealSheafMap i)

/-- The associated ideal sheaf of a morphism of algebraic spaces, as an
`𝒪_X`-module. -/
noncomputable abbrev idealSheaf {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) : X.Modules :=
  (idealSheafSubobject i).toModule

/-- The canonical inclusion of the associated ideal sheaf into `𝒪_X`. -/
noncomputable abbrev idealSheafι {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) :
    idealSheaf i ⟶ SheafOfModules.unit (structureSheaf X) :=
  (idealSheafSubobject i).arrow

/-- The associated ideal sheaf of `i` is the kernel of `𝒪_X ⟶ i_* 𝒪_Z`. -/
noncomputable def idealSheaf_spec {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) : idealSheaf i ≅ kernel (idealSheafMap i) :=
  kernelSubobjectIso (idealSheafMap i)

/-- The subobject arrow of the associated ideal sheaf is the canonical
inclusion into `𝒪_X`. -/
theorem idealSheafSubobject_arrow {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) : (idealSheafSubobject i).arrow = idealSheafι i :=
  sorry

/-- The inclusion of the associated ideal sheaf is annihilated by
`𝒪_X ⟶ i_* 𝒪_Z`. -/
theorem idealSheafι_comp_map {S : Scheme.{u}} {Z X : AlgebraicSpace S}
    (i : Z ⟶ X) : idealSheafι i ≫ idealSheafMap i = 0 :=
  sorry

/-- The associated ideal sheaf of a closed immersion of algebraic spaces is
quasi-coherent. -/
instance instIsQuasiCoherent_idealSheafSubobject {S : Scheme.{u}}
    {Z X : AlgebraicSpace S} (i : Z ⟶ X) [IsClosedImmersion i] :
    IsQuasiCoherent (idealSheafSubobject i) :=
  sorry

end Hom

end AlgebraicGeometry.AlgebraicSpace
