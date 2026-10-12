/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Quasicoherent.Pullback
public import stacks_project.Chap56.«56_5_1_1_FourierMukai»

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.QCoh

/-- The tensor unit of `X.Modules` is quasicoherent. -/
instance tensorUnit_isQuasicoherent (X : Scheme.{u}) :
    (𝟙_ X.Modules).IsQuasicoherent := sorry

/-- The structure sheaf `O_X` as an object of `Scheme.QCoh X`. -/
noncomputable def structureSheaf (X : Scheme.{u}) : Scheme.QCoh X :=
  ⟨𝟙_ X.Modules, tensorUnit_isQuasicoherent X⟩

/-- The underlying module of `structureSheaf X` is the tensor unit of `X.Modules`. -/
theorem structureSheaf_obj (X : Scheme.{u}) :
    (structureSheaf X).obj = 𝟙_ X.Modules := sorry

/-- The external product `A ⊠ B` of quasicoherent modules on a fibre product. -/
noncomputable def boxProduct {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (A : Scheme.QCoh X) (B : Scheme.QCoh Y) :
    Scheme.QCoh (Limits.pullback f g) :=
  (tensorRight ((pullback (Limits.pullback.snd f g)).obj B)).obj
    ((pullback (Limits.pullback.fst f g)).obj A)

/-- The underlying module of `boxProduct f g A B` is
`pr₁^* A ⊗ pr₂^* B` on `Limits.pullback f g`. -/
theorem boxProduct_obj {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (A : Scheme.QCoh X) (B : Scheme.QCoh Y) :
    (boxProduct f g A B).obj =
      ((pullback (Limits.pullback.fst f g)).obj A).obj ⊗
        ((pullback (Limits.pullback.snd f g)).obj B).obj := sorry

end AlgebraicGeometry.Scheme.QCoh
