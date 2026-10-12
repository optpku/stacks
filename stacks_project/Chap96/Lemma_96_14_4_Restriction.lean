/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_16_5_Quotient
public import stacks_project.Chap96.Lemma_96_14_2_Restriction
public import stacks_project.Chap96.«96_10_3_3_Comparison»

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

/-- Identity presentation of an algebraic space as a category fibred in
groupoids. -/
def idSpace (X : AlgebraicSpace S) : X.toGroupoids ≌ X.toGroupoids :=
  Bicategory.Equivalence.id _

/-- `idSpace X` is the identity equivalence on `X.toGroupoids`. -/
theorem idSpace_eq (X : AlgebraicSpace S) :
    idSpace X = Bicategory.Equivalence.id _ :=
  rfl

variable {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)

/-- Restriction of an `𝒪_[U / R]`-module to the small étale site of `U`, as
`x^* M |_{U_étale}`. -/
def atlasRestrictModules (M : RingedSite.ModuleCat.{u} (fppfRingedSite G.quotientStack)) :
    SheafOfModules.{u} (AlgebraicSpace.structureSheaf G.U.left) :=
  (restrictModules (idSpace G.U.left)).obj
    ((etaleModuleInverseImage G.atlas).obj ((toEtaleRingedModules G.quotientStack).obj M))

/-- `atlasRestrictModules G M` is restriction of the étale inverse image of `M` along
the atlas. -/
theorem atlasRestrictModules_eq
    (M : RingedSite.ModuleCat.{u} (fppfRingedSite G.quotientStack)) :
    atlasRestrictModules G M =
      (restrictModules (idSpace G.U.left)).obj
        ((etaleModuleInverseImage G.atlas).obj
          ((toEtaleRingedModules G.quotientStack).obj M)) :=
  rfl

/-- The map `Hom_{𝒪_𝒳}(ℱ, ℋ) → Hom_{𝒪_U}(x^* ℱ |_{U_étale}, x^* ℋ |_{U_étale})`
sending `φ` to `x^* φ |_{U_étale}`. -/
def atlasRestrictHom (F : QCoh G.quotientStack)
    (H : RingedSite.ModuleCat.{u} (fppfRingedSite G.quotientStack)) :
    (F.obj ⟶ H) →
      (atlasRestrictModules G F.obj ⟶ atlasRestrictModules G H) :=
  fun ψ ↦
    (restrictModules (idSpace G.U.left)).map
      ((etaleModuleInverseImage G.atlas).map
        ((toEtaleRingedModules G.quotientStack).map ψ))

/-- `atlasRestrictHom` is restriction of the étale inverse image of `ψ` along the
atlas. -/
theorem atlasRestrictHom_app (F : QCoh G.quotientStack)
    (H : RingedSite.ModuleCat.{u} (fppfRingedSite G.quotientStack))
    (ψ : F.obj ⟶ H) :
    atlasRestrictHom G F H ψ =
      (restrictModules (idSpace G.U.left)).map
        ((etaleModuleInverseImage G.atlas).map
          ((toEtaleRingedModules G.quotientStack).map ψ)) :=
  rfl

end AlgebraicGeometry.GroupoidsOver
