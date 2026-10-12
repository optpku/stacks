/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
public import stacks_project.Chap95.«95_18_2_1_Stack»

/-!
# Induced functor to a 2-fibre product of stacks

A 2-commutative square of stacks in groupoids over `(Sch/S)_fppf` induces a
canonical 1-morphism into the 2-fibre product `𝒴' ×_𝒴 𝒳`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- The 2-commutative square with apex `𝒳'`, first leg `F'`, second leg `G`,
and comparison cell `γ : F' ≫ H ≅ G ≫ F`. -/
def squareCone (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) :
    PseudoPullbackCone H F where
  pt := 𝒳'
  fst := F'
  snd := G
  iso := γ

/-- The induced functor `𝒳' ⟶ 𝒴' ×_𝒴 𝒳` of a 2-commutative square, as the
universal lift of `squareCone` into the canonical 2-fibre product of `H` and
`F`. -/
noncomputable def toFibreProduct (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) :
    𝒳' ⟶
      StackOver.Groupoids.TwoFibreProduct.apex.{u + 1, u, u + 1, u} H F :=
  PseudoPullbackCone.lift (squareCone F' F G H γ)
    (StackOver.Groupoids.TwoFibreProduct.cone.{u + 1, u, u + 1, u} H F)

/-- `toFibreProduct` is the universal lift of `squareCone` into the 2-fibre
product of `H` and `F`. -/
theorem toFibreProduct_eq (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) :
    toFibreProduct F' F G H γ =
      PseudoPullbackCone.lift (squareCone F' F G H γ)
        (StackOver.Groupoids.TwoFibreProduct.cone.{u + 1, u, u + 1, u} H F) :=
  sorry

/-- The first projection of `toFibreProduct` is isomorphic to `F'`. -/
noncomputable def toFibreProduct_fst (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) :
    toFibreProduct F' F G H γ ≫
        StackOver.Groupoids.TwoFibreProduct.fst.{u + 1, u, u + 1, u} H F ≅
      F' :=
  PseudoPullbackCone.lift.fstIso (squareCone F' F G H γ)
    (StackOver.Groupoids.TwoFibreProduct.cone.{u + 1, u, u + 1, u} H F)

/-- The second projection of `toFibreProduct` is isomorphic to `G`. -/
noncomputable def toFibreProduct_snd (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴)
    (G : 𝒳' ⟶ 𝒳) (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) :
    toFibreProduct F' F G H γ ≫
        StackOver.Groupoids.TwoFibreProduct.snd.{u + 1, u, u + 1, u} H F ≅
      G :=
  PseudoPullbackCone.lift.sndIso (squareCone F' F G H γ)
    (StackOver.Groupoids.TwoFibreProduct.cone.{u + 1, u, u + 1, u} H F)

end AlgebraicGeometry.FiniteHilbertStack
