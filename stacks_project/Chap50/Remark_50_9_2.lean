/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import stacks_project.Chap50.Remark_50_9_2_ChernClass

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

/- Remark 50.9.2
The logarithmic class of an invertible module maps to the de Rham first Chern class,
and finite cup products map to the corresponding de Rham and Hodge products in the
expected Hodge-filtration stages. -/
@[stacks 0FME] #check (AlgebraicGeometry.Scheme.DeRham.hodgeMap_gammaCupProduct :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (C : ChernClassContext f) {a : ℕ}
    (L : Fin a → X.Modules) [∀ i, Scheme.Modules.Invertible (L i)],
    (hodgeMap f (a : ℤ) (2 * (a : ℤ))).hom (gammaCupProduct f C L) =
      C.deRhamCupProduct
        (fun i ↦ C.deRhamFirstChern (Scheme.Modules.picardClass (L i))))

#check (gammaOne : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (C : ChernClassContext f)
  (L : X.Modules) [Scheme.Modules.Invertible L], hodgeSource f 1 2)
#check (hodgeMap_gammaOne : ∀ {X S : Scheme.{u}} (f : X ⟶ S) (C : ChernClassContext f)
  (L : X.Modules) [Scheme.Modules.Invertible L],
  (hodgeMap f 1 2).hom (gammaOne f C L) =
    C.deRhamFirstChern (Scheme.Modules.picardClass L))
#check (hodgeProjection_gammaOne : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
  (C : ChernClassContext f) (L : X.Modules) [Scheme.Modules.Invertible L],
  C.hodgeProjection 1 (gammaOne f C L) =
    C.hodgeFirstChern (Scheme.Modules.picardClass L))
#check (deRhamFirstChern_mem_hodgeFiltration :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (C : ChernClassContext f)
    (L : X.Modules) [Scheme.Modules.Invertible L],
    ∃ z : hodgeFiltrationStage f 2 1,
      ((hodgeFiltration f 2).stage 1).arrow.hom z =
        C.deRhamFirstChern (Scheme.Modules.picardClass L))
#check (gammaCupProduct : ∀ {X S : Scheme.{u}} (f : X ⟶ S)
  (C : ChernClassContext f) {a : ℕ} (L : Fin a → X.Modules)
  [∀ i, Scheme.Modules.Invertible (L i)], hodgeSource f (a : ℤ) (2 * (a : ℤ)))
#check (deRhamFirstChernCupProduct_mem_hodgeFiltration :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (C : ChernClassContext f) {a : ℕ}
    (L : Fin a → X.Modules) [∀ i, Scheme.Modules.Invertible (L i)],
    ∃ z : hodgeFiltrationStage f (2 * (a : ℤ)) (a : ℤ),
      ((hodgeFiltration f (2 * (a : ℤ))).stage (a : ℤ)).arrow.hom z =
        C.deRhamCupProduct
          (fun i ↦ C.deRhamFirstChern (Scheme.Modules.picardClass (L i))))
#check (hodgeProjection_gammaCupProduct :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (C : ChernClassContext f) {a : ℕ}
    (L : Fin a → X.Modules) [∀ i, Scheme.Modules.Invertible (L i)],
    C.hodgeProjection a (gammaCupProduct f C L) =
      C.hodgeCupProduct
        (fun i ↦ C.hodgeFirstChern (Scheme.Modules.picardClass (L i))))

end AlgebraicGeometry.Scheme.DeRham
