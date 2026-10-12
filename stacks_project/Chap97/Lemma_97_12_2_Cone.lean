/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Bilimit.Lift
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.Cone
public import ReasLib.CategoryTheory.Fibered.Stack.TwoFibreProduct.Basic
public import stacks_project.Chap95.«95_18_2_1_Forgetful»
public import stacks_project.Chap97.Lemma_97_12_1_Map

/-!
# Forgetful Hilbert square

A 2-commutative square of stacks in groupoids over `(Sch/S)_fppf` and a degree `d`
induce a readable pseudopullback cone whose apex is `H_d(𝒳'/𝒴')`, whose first
leg is the forgetful 1-morphism to `𝒴'`, and whose second leg is the induced
1-morphism of finite Hilbert stacks.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Bicategory
open AlgebraicGeometry.FiniteHilbertStack
open StackOver.Groupoids.Hom
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.FiniteHilbertStack

variable {S : Scheme.{u}}
variable {𝒳' 𝒳 𝒴' 𝒴 :
    StackOver.Groupoids.{u + 1, u, u + 1, u} (Scheme.fppfTopology.over S)}

/-- The readable square with apex `H_d(𝒳'/𝒴')`, first leg `forgetToY F' d`,
second leg `mapSquare F' F G H γ d`, and bottom cospan `H` and
`forgetToY F d`. -/
def forgetToYSquare (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅ mapSquare F' F G H γ d ≫ forgetToY F d) :
    PseudoPullbackCone H (forgetToY F d) where
  pt := stack (toGroupoidsMor F') d
  fst := forgetToY F' d
  snd := mapSquare F' F G H γ d
  iso := comm

/-- The apex of `forgetToYSquare` is the finite Hilbert stack `H_d(𝒳'/𝒴')`. -/
theorem forgetToYSquare_pt (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅ mapSquare F' F G H γ d ≫ forgetToY F d) :
    (forgetToYSquare F' F G H γ d comm).pt = stack (toGroupoidsMor F') d :=
  sorry

/-- The first leg of `forgetToYSquare` is the forgetful 1-morphism
`H_d(𝒳'/𝒴') ⟶ 𝒴'`. -/
theorem forgetToYSquare_fst (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅ mapSquare F' F G H γ d ≫ forgetToY F d) :
    (forgetToYSquare F' F G H γ d comm).fst = forgetToY F' d :=
  sorry

/-- The second leg of `forgetToYSquare` is the induced 1-morphism
`H_d(𝒳'/𝒴') ⟶ H_d(𝒳/𝒴)`. -/
theorem forgetToYSquare_snd (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅ mapSquare F' F G H γ d ≫ forgetToY F d) :
    (forgetToYSquare F' F G H γ d comm).snd = mapSquare F' F G H γ d :=
  sorry

/-- The comparison cell of `forgetToYSquare` is the supplied 2-isomorphism. -/
theorem forgetToYSquare_iso (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅ mapSquare F' F G H γ d ≫ forgetToY F d) :
    (forgetToYSquare F' F G H γ d comm).iso = comm :=
  sorry

/-- The comparison 1-morphism `H_d(𝒳'/𝒴') ⟶ 𝒴' ×_𝒴 H_d(𝒳/𝒴)` into the
canonical 2-fibre product of `H` with `forgetToY F d`. -/
def forgetToYSquare.lift (F' : 𝒳' ⟶ 𝒴') (F : 𝒳 ⟶ 𝒴) (G : 𝒳' ⟶ 𝒳)
    (H : 𝒴' ⟶ 𝒴) (γ : F' ≫ H ≅ G ≫ F) (d : ℕ)
    (comm : forgetToY F' d ≫ H ≅ mapSquare F' F G H γ d ≫ forgetToY F d) :
    (forgetToYSquare F' F G H γ d comm).pt ⟶
      StackOver.Groupoids.TwoFibreProduct.apex.{u + 1, u, u + 1, u}
        H (forgetToY F d) :=
  PseudoPullbackCone.lift (forgetToYSquare F' F G H γ d comm)
    (StackOver.Groupoids.TwoFibreProduct.cone.{u + 1, u, u + 1, u}
      H (forgetToY F d))

end AlgebraicGeometry.FiniteHilbertStack
