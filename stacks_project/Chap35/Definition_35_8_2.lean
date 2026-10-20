/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.AssociatedModule
import StacksCheckRecall

@[expose] public section

open CategoryTheory Opposite
open AlgebraicGeometry

universe u

/- Definition 35.8.2 (1): the structure sheaf on the big standard `τ`-site sends
`T ⟶ S` to `Γ(T, 𝒪_T)`. -/
@[stacks 03DU] #check (AlgebraicGeometry.StandardTopology.Big.structureSheaf :
  ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u}),
    Sheaf (τ.overTopology S) RingCat.{u})

#check (AlgebraicGeometry.StandardTopology.Big.structureSheaf_obj :
  ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u})
    (U : CategoryTheory.Over S),
    (AlgebraicGeometry.StandardTopology.Big.structureSheaf τ S).obj.obj (op U) =
      RingCat.of (Γ(U.left, ⊤)))

/- Definition 35.8.2 (2): the structure sheaf on the small Zariski site sends
`T ⟶ S` to `Γ(T, 𝒪_T)`. -/
@[stacks 03DU] #check (AlgebraicGeometry.Scheme.Zariski.Small.structureSheaf :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    Sheaf S.smallZariskiTopology RingCat.{u})

#check (AlgebraicGeometry.Scheme.Zariski.Small.structureSheaf_obj :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (U : S.smallZariskiSite),
    (AlgebraicGeometry.Scheme.Zariski.Small.structureSheaf S).obj.obj (op U) =
      RingCat.of (Γ(U.left, ⊤)))

/- Definition 35.8.2 (3): the structure sheaf on the small étale site sends
`T ⟶ S` to `Γ(T, 𝒪_T)`. -/
@[stacks 03DU] #check (AlgebraicGeometry.Scheme.Etale.Small.structureSheaf :
  ∀ S : AlgebraicGeometry.Scheme.{u},
    Sheaf S.smallEtaleTopology RingCat.{u})

#check (AlgebraicGeometry.Scheme.Etale.Small.structureSheaf_obj :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (U : S.Etale),
    (AlgebraicGeometry.Scheme.Etale.Small.structureSheaf S).obj.obj (op U) =
      RingCat.of (Γ(U.left, ⊤)))

/- Definition 35.8.2 (4): a quasi-coherent module `F` on `S` determines the big-site
module sheaf whose value at `f : T ⟶ S` is `Γ(T, f^*F)`. -/
@[stacks 03DU] #check (AlgebraicGeometry.StandardTopology.Big.associatedModule :
  ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent],
    SheafOfModules (AlgebraicGeometry.StandardTopology.Big.structureSheaf τ S))

#check (AlgebraicGeometry.StandardTopology.Big.associatedModule_obj :
  ∀ (τ : AlgebraicGeometry.StandardTopology) (S : AlgebraicGeometry.Scheme.{u})
    (F : S.Modules) [F.IsQuasicoherent] (U : CategoryTheory.Over S),
    (AlgebraicGeometry.StandardTopology.Big.associatedModule τ S F).val.obj (op U) =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj
        (𝟭 (CategoryTheory.Over S)) F (op U))

/- Definition 35.8.2 (5): a quasi-coherent module `F` on `S` determines the small
Zariski module sheaf whose value at `f : T ⟶ S` is `Γ(T, f^*F)`. -/
@[stacks 03DU] #check (AlgebraicGeometry.Scheme.Zariski.Small.associatedModule :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent],
    SheafOfModules (AlgebraicGeometry.Scheme.Zariski.Small.structureSheaf S))

#check (AlgebraicGeometry.Scheme.Zariski.Small.associatedModule_obj :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : S.smallZariskiSite),
    (AlgebraicGeometry.Scheme.Zariski.Small.associatedModule S F).val.obj (op U) =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj
        S.smallZariskiForget F (op U))

/- Definition 35.8.2 (6): a quasi-coherent module `F` on `S` determines the small étale
module sheaf whose value at `f : T ⟶ S` is `Γ(T, f^*F)`. -/
@[stacks 03DU] #check (AlgebraicGeometry.Scheme.Etale.Small.associatedModule :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent],
    SheafOfModules (AlgebraicGeometry.Scheme.Etale.Small.structureSheaf S))

#check (AlgebraicGeometry.Scheme.Etale.Small.associatedModule_obj :
  ∀ (S : AlgebraicGeometry.Scheme.{u}) (F : S.Modules) [F.IsQuasicoherent]
    (U : S.Etale),
    (AlgebraicGeometry.Scheme.Etale.Small.associatedModule S F).val.obj (op U) =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsObj
        (AlgebraicGeometry.Scheme.Etale.forget S) F (op U))
