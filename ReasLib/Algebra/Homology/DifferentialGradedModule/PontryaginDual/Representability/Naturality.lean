/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Left.Forget
public import ReasLib.Algebra.Homology.DifferentialGradedModule.PontryaginDual.Representability

/-!
# Functorial Pontryagin representability

Pontryagin representability is contravariantly natural in the right differential graded module.
This file packages the pointwise linear equivalences as isomorphisms of `ModuleCat`-valued
functors.  The pointwise comparison remains available as the component API.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory DifferentialGradedCategory
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedModule.PontryaginRepresentable

variable {R : Type u} [CommRing R]

namespace Functor

/-- The contravariant functor `M ↦ Hom_A(M, Aᵛ[k])` on right differential graded modules. -/
@[stacks 09K4 "shifted Hom functor into the Pontryagin dual regular module"]
def hom (A : CochainDGAlgebra.{u, v} R) (k : ℤ) :
    (DifferentialGradedModule.{u, v} A)ᵒᵖ ⥤ ModuleCat.{v} R :=
  (linearYoneda R (DifferentialGradedModule.{u, v} A)).obj Aᵛ[k]

/-- The contravariant functor taking `M` to the degree-`k` cycles of `Mᵛ`. -/
@[stacks 09K4 "cycle functor of the Pontryagin dual"]
def cycles (A : CochainDGAlgebra.{u, v} R) (k : ℤ) :
    (DifferentialGradedModule.{u, v} A)ᵒᵖ ⥤ ModuleCat.{v} R :=
  DifferentialGradedModule.pontryaginDualFunctor A ⋙
    LeftDifferentialGradedModule.cyclesFunctor A k

/-- The contravariant functor `M ↦ Hom_K(M, Aᵛ[k])` on right differential graded modules. -/
@[stacks 09K4 "shifted Homotopy-category functor into the Pontryagin dual"]
def homotopy (A : CochainDGAlgebra.{u, v} R) (k : ℤ) :
    (DifferentialGradedModule.{u, v} A)ᵒᵖ ⥤ ModuleCat.{v} R :=
  (toK A).op ⋙
    (linearYoneda R
      (DifferentialGradedCategory.K R (DifferentialGradedModule.{u, v} A))).obj
        ((toK A).obj Aᵛ[k])

/-- The contravariant functor taking `M` to the degree-`k` homology of `Mᵛ`. -/
@[stacks 09K4 "homology functor of the Pontryagin dual"]
def homology (A : CochainDGAlgebra.{u, v} R) (k : ℤ) :
    (DifferentialGradedModule.{u, v} A)ᵒᵖ ⥤ ModuleCat.{v} R :=
  DifferentialGradedModule.pontryaginDualFunctor A ⋙
    LeftDifferentialGradedModule.homologyFunctor A k

end Functor

/-- The pointwise `ModuleCat` isomorphism from shifted morphisms to dual cycles. -/
@[stacks 09K4 "pointwise shifted-Hom to dual-cycles comparison"]
def homCyclesApp (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (Functor.hom A k).obj M ≅ (Functor.cycles A k).obj M :=
  (homLinearEquivDualCycles M.unop k).toModuleIso

/-- The forward morphism of the pointwise comparison is the canonical representability map. -/
@[simp, stacks 09K4 "forward shifted-Hom to dual-cycles comparison"]
theorem homCyclesApp_hom (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homCyclesApp A k M).hom =
      ModuleCat.ofHom (homLinearEquivDualCycles M.unop k).toLinearMap := sorry

/-- The inverse morphism of the pointwise comparison is the inverse representability map. -/
@[simp, stacks 09K4 "inverse dual-cycles to shifted-Hom comparison"]
theorem homCyclesApp_inv (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homCyclesApp A k M).inv =
      ModuleCat.ofHom (homLinearEquivDualCycles M.unop k).symm.toLinearMap := sorry

/-- The shifted-morphism comparison with dual cycles is natural in the right DG module. -/
@[reassoc, stacks 09K4 "naturality of the shifted-Hom to dual-cycles comparison"]
theorem homCyclesApp_naturality (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    {M N : (DifferentialGradedModule.{u, v} A)ᵒᵖ} (f : M ⟶ N) :
    (Functor.hom A k).map f ≫ (homCyclesApp A k N).hom =
      (homCyclesApp A k M).hom ≫ (Functor.cycles A k).map f := sorry

/-- Lemma 22.19.3 (1) (09K4): `Hom_A(M, Aᵛ[k])` and `Z^k(Mᵛ)` are naturally isomorphic
as contravariant `ModuleCat R`-valued functors in `M`. -/
@[stacks 09K4 "shifted morphisms into the dual regular module as a functor"]
def homCyclesIso (A : CochainDGAlgebra.{u, v} R) (k : ℤ) :
    Functor.hom A k ≅ Functor.cycles A k :=
  NatIso.ofComponents (homCyclesApp A k) (homCyclesApp_naturality A k)

/-- The component of `homCyclesIso` is the canonical pointwise representability isomorphism. -/
@[simp]
theorem homCyclesIso_app (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homCyclesIso A k).app M = homCyclesApp A k M := sorry

/-- The forward morphism of `homCyclesIso` is its pointwise forward comparison. -/
@[simp, stacks 09K4 "forward component of the shifted-Hom to dual-cycles isomorphism"]
theorem homCyclesIso_hom_app (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homCyclesIso A k).hom.app M = (homCyclesApp A k M).hom := sorry

/-- The inverse morphism of `homCyclesIso` is its pointwise inverse comparison. -/
@[simp, stacks 09K4 "inverse component of the shifted-Hom to dual-cycles isomorphism"]
theorem homCyclesIso_inv_app (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homCyclesIso A k).inv.app M = (homCyclesApp A k M).inv := sorry

/-- The pointwise `ModuleCat` isomorphism from shifted homotopy morphisms to dual homology. -/
@[stacks 09K4 "pointwise shifted-homotopy to dual-homology comparison"]
def homotopyHomologyApp (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (Functor.homotopy A k).obj M ≅ (Functor.homology A k).obj M :=
  (homotopyLinearEquivDualHomology M.unop k).toModuleIso

/-- The forward morphism of the pointwise homotopy comparison is the canonical map. -/
@[simp, stacks 09K4 "forward shifted-homotopy to dual-homology comparison"]
theorem homotopyHomologyApp_hom (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homotopyHomologyApp A k M).hom =
      ModuleCat.ofHom (homotopyLinearEquivDualHomology M.unop k).toLinearMap := sorry

/-- The inverse morphism of the pointwise homotopy comparison is the inverse canonical map. -/
@[simp, stacks 09K4 "inverse dual-homology to shifted-homotopy comparison"]
theorem homotopyHomologyApp_inv (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homotopyHomologyApp A k M).inv =
      ModuleCat.ofHom (homotopyLinearEquivDualHomology M.unop k).symm.toLinearMap := sorry

/-- The shifted-homotopy comparison with dual homology is natural in the right DG module. -/
@[reassoc, stacks 09K4 "naturality of the shifted-homotopy to dual-homology comparison"]
theorem homotopyHomologyApp_naturality (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    {M N : (DifferentialGradedModule.{u, v} A)ᵒᵖ} (f : M ⟶ N) :
    (Functor.homotopy A k).map f ≫ (homotopyHomologyApp A k N).hom =
      (homotopyHomologyApp A k M).hom ≫ (Functor.homology A k).map f := sorry

/-- Lemma 22.19.3 (2) (09K4): `Hom_K(M, Aᵛ[k])` and `H^k(Mᵛ)` are naturally isomorphic
as contravariant `ModuleCat R`-valued functors in `M`. -/
@[stacks 09K4 "shifted homotopy morphisms into the dual regular module as a functor"]
def homotopyHomologyIso (A : CochainDGAlgebra.{u, v} R) (k : ℤ) :
    Functor.homotopy A k ≅ Functor.homology A k :=
  NatIso.ofComponents (homotopyHomologyApp A k)
    (homotopyHomologyApp_naturality A k)

/-- The component of `homotopyHomologyIso` is the canonical pointwise homotopy comparison. -/
@[simp]
theorem homotopyHomologyIso_app (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homotopyHomologyIso A k).app M = homotopyHomologyApp A k M := sorry

/-- The forward morphism of `homotopyHomologyIso` is its pointwise forward comparison. -/
@[simp, stacks 09K4 "forward component of the shifted-homotopy to dual-homology isomorphism"]
theorem homotopyHomologyIso_hom_app (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homotopyHomologyIso A k).hom.app M = (homotopyHomologyApp A k M).hom := sorry

/-- The inverse morphism of `homotopyHomologyIso` is its pointwise inverse comparison. -/
@[simp, stacks 09K4 "inverse component of the shifted-homotopy to dual-homology isomorphism"]
theorem homotopyHomologyIso_inv_app (A : CochainDGAlgebra.{u, v} R) (k : ℤ)
    (M : (DifferentialGradedModule.{u, v} A)ᵒᵖ) :
    (homotopyHomologyIso A k).inv.app M = (homotopyHomologyApp A k M).inv := sorry

end DifferentialGradedModule.PontryaginRepresentable
