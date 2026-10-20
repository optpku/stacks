module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Tor
public import ReasLib.Algebra.Category.ModuleCat.Tor.Independence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Flat base change for Tor independence

@stack 0FXF

Tor independence of bundled modules is preserved by flat extension of scalars.  A companion
statement identifies the algebra-facing tensor-product form used in the Stacks Project.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u

namespace CategoryTheory.ModuleCat.Tor.IsIndependent

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Flat extension of scalars preserves Tor independence of bundled modules. -/
@[stacks 0FXF "flat base change for bundled Tor independence"]
theorem baseChange_extendScalars {M N : ModuleCat.{u} R} (h : IsIndependent M N)
    (f : R →+* S) (hf : f.Flat) :
    IsIndependent ((ModuleCat.extendScalars f).obj M) ((ModuleCat.extendScalars f).obj N) := sorry

-- Local instance justification (instance diamond): this is the source-facing `A ⊗[R] S`
-- orientation of the canonical tensor-product algebra, used only by the specialization below.
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- Flat base change preserves Tor independence after tensoring both commutative algebras
with the flat base algebra. -/
@[stacks 0FXF "flat base change for algebra Tor independence"]
theorem baseChange_tensorProduct
    {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra R S] [Module.Flat R S]
    (h : IsIndependent (ModuleCat.of R A) (ModuleCat.of R B)) :
    IsIndependent (ModuleCat.of S (A ⊗[R] S)) (ModuleCat.of S (B ⊗[R] S)) := sorry

end CategoryTheory.ModuleCat.Tor.IsIndependent
