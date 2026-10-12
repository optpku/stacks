/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap69.Lemma_69_12_5_Monoidal

/-!
# Tensor of a module with the pullback of a module on algebraic spaces

The source module `F ⊗_{𝒪_X} f^* G` is the monoidal tensor of `F` with the
module pullback of `G`, obtained by transporting `moduleTensor` along the
commutative presentation of `𝒪_X`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- The tensor product of an `𝒪_X`-module with the pullback of an `𝒪_Y`-module. -/
noncomputable def tensorPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) (G : Y.Modules) : X.Modules :=
  tensorObj F ((pullback f).obj G)

/-- `tensorPullback F f G` is the commutative presentation tensor of `F` with
`f^* G`, transported along `toCommModules` / `ofCommModules`. -/
theorem tensorPullback_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) (G : Y.Modules) :
    tensorPullback F f G =
      (ofCommModules X).obj
        (tensorObj ((toCommModules X).obj F)
          ((toCommModules X).obj ((pullback f).obj G))) :=
  sorry

/-- The tensor product of a quasi-coherent module with the pullback of a
quasi-coherent module is quasi-coherent. -/
instance isQuasicoherent_tensorPullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (F : X.Modules) (f : X ⟶ Y) (G : Y.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] :
    (tensorPullback F f G).IsQuasicoherent :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
