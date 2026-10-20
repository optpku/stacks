/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.BaseChange
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.DifferentialGraded.Module.Flat.Acyclic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 24.23.8

The left-module category and relative tensor product are the canonical bimodule-object
constructions.  The fixed-base tensor clause is owned by the DG-module flatness API, while the
generic base-change functor is assembled from monoidal transport and extension of scalars.

The full second clause quantifies over arbitrary `RingedSite.ToposHom`.  It is intentionally not
identified with the weaker site-presented pullback: it still needs a monoidal complex, DG-algebra,
and DG-module base-change bridge for arbitrary topos morphisms.
-/

open CategoryTheory
open scoped SheafOfModules.RingedSite.DifferentialGradedAlgebra
open scoped SheafOfModules.RingedSite.DifferentialGradedModule
open scoped SheafOfModules.RingedSite.LeftDifferentialGradedModule

noncomputable section

universe uC vC wC uD vD wD

namespace SheafOfModules.RingedSite.DifferentialGradedModule

variable {C : Type uC} [Category.{vC} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
variable [HasWeakSheafify J AddCommGrpCat.{wC}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
variable {O : Sheaf J CommRingCat.{wC}}
variable (A : DGA(O)) (P : Mod(A, d)) (N : LMod(A, d))

/- Lemma 24.23.8 (1): left differential graded modules and their relative tensor product use the
canonical balanced tensor construction. -/
@[stacks 0FSI "(1), canonical left DG modules"]
#check (DifferentialGradedAlgebra.LeftModule A)

@[stacks 0FSI "(1), canonical relative tensor product"]
#check
  (DifferentialGradedModule.tensor P N :
    CochainComplex
      (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O)) ℤ)

/- Lemma 24.23.8 (1): a fixed-base good acyclic right DG module has acyclic tensor product with
every left DG module. -/
@[stacks 0FSI "(1), acyclic tensor product"]
#check
  (IsGoodAtBase.tensor_acyclic (P := P) :
    IsGoodAtBase P → HomologicalComplex.Acyclic P.toComplex →
      ∀ N : LMod(A, d), HomologicalComplex.Acyclic (tensor P N))

/- Lemma 24.23.8 (2), reusable algebraic infrastructure: a lax monoidal functor on cochain
complexes together with a map of transported DG algebras induces the canonical DG-module base
change functor.  A geometric `RingedSite.ToposHom` specialization still requires a separate
owner. -/
section BaseChangeBoundary

variable {D : Type uD} [Category.{vD} D] {JD : GrothendieckTopology D}
variable [JD.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
variable [HasWeakSheafify JD AddCommGrpCat.{wD}]
variable [JD.WEqualsLocallyBijective AddCommGrpCat.{wD}]
variable {OD : Sheaf JD CommRingCat.{wD}}
variable (F : CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := J) (𝒪 := O)) ℤ ⥤
  CochainComplex
    (DifferentialGradedAlgebra.moduleCategory (J := JD) (𝒪 := OD)) ℤ)
variable [F.LaxMonoidal] {B : DGA(OD)}
variable (φ : (DifferentialGradedAlgebra.map F).obj A ⟶ B)

@[stacks 0FSI "(2), algebraic base-change boundary"]
#check (DifferentialGradedModule.baseChange F φ : Mod(A, d) ⥤ Mod(B, d))

end BaseChangeBoundary

end SheafOfModules.RingedSite.DifferentialGradedModule

end
