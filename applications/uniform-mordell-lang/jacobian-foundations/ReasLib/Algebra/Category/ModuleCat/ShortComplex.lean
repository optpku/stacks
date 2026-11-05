module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Tactic.CrossRefAttribute

/-!
# Short complexes of modules

@stack 010G

This leaf gives the standard linear-equivalence views of a short exact sequence in `ModuleCat`
and the concrete product model attached to a splitting.  These constructions are independent of
finiteness, coherence, or a derived-functor application.
-/

@[expose] public section

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- In a short exact sequence of `R`-modules, the source identifies with the
kernel of the second map. -/
noncomputable def sourceEquivKer (hS : S.ShortExact) :
    S.X₁ ≃ₗ[R] LinearMap.ker S.g.hom :=
  (LinearEquiv.ofInjective S.f.hom hS.moduleCat_injective_f).trans
    (LinearEquiv.ofEq _ _ hS.exact.moduleCat_range_eq_ker)

/-- In a short exact sequence of `R`-modules, the quotient of the middle
term by the range of the first map identifies with the target. -/
noncomputable def quotientRangeEquivTarget (hS : S.ShortExact) :
    (S.X₂ ⧸ LinearMap.range S.f.hom) ≃ₗ[R] S.X₃ :=
  (Submodule.quotEquivOfEq _ _ hS.exact.moduleCat_range_eq_ker).trans
    (LinearMap.quotKerEquivOfSurjective S.g.hom hS.moduleCat_surjective_g)

end CategoryTheory.ShortComplex.ShortExact

namespace CategoryTheory.ShortComplex.Splitting

variable {R : Type u} [Ring R]
variable {S : ShortComplex (ModuleCat.{v} R)}

/-- The concrete product-to-middle isomorphism determined by a splitting of a short complex of
modules. -/
@[stacks 010G "concrete product isomorphism from a module splitting"]
noncomputable def prodIso (s : S.Splitting) :
    ModuleCat.of R (S.X₁ × S.X₃) ≅ S.X₂ :=
  (s.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd S.X₁ S.X₃).symm

/-- The left product inclusion followed by the splitting product isomorphism is the first map of
the short complex. -/
@[reassoc (attr := simp), stacks 010G "left inclusion of a module splitting"]
theorem inl_prodIso_hom (s : S.Splitting) :
    ModuleCat.ofHom (LinearMap.inl R S.X₁ S.X₃) ≫ s.prodIso.hom = S.f := sorry

/-- The right product inclusion followed by the splitting product isomorphism is the chosen
section of the second map. -/
@[reassoc (attr := simp), stacks 010G "right inclusion of a module splitting"]
theorem inr_prodIso_hom (s : S.Splitting) :
    ModuleCat.ofHom (LinearMap.inr R S.X₁ S.X₃) ≫ s.prodIso.hom = s.s := sorry

end CategoryTheory.ShortComplex.Splitting
