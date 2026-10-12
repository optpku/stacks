/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Cohomology.MayerVietoris

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace EtaleMayerVietoris

variable {X : Scheme.{u}}
variable [HasWeakSheafify X.smallEtaleTopology (Type u)]
variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u})]
variable (U V : X.Opens) (hUV : U ⊔ V = ⊤)

#check (square X U V hUV : X.smallEtaleTopology.MayerVietorisSquare)
#check (openSquare X U V : Square X.Etale)
variable (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u})

#check (mapAt (X := X) (𝟙 F) 0 (Scheme.Etale.mk (𝟙 X)) :
    F.H' 0 (Scheme.Etale.mk (𝟙 X)) ⟶ F.H' 0 (Scheme.Etale.mk (𝟙 X)))
#check (sequenceFunctor (square X U V hUV) 0 :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u} ⥤
      ComposableArrows AddCommGrpCat.{u} 5)
#check (mayerVietorisEtaleExact X U V hUV :
    ∀ F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u},
      (((square X U V hUV).sequence F 0 1 rfl).zeroPrecomp 1).Exact ∧
        ∀ n : ℕ, ((square X U V hUV).sequence F n (n + 1) rfl).Exact)

end EtaleMayerVietoris
