module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower
public import ReasLib.RingTheory.Topology.Adic.InverseLimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic topology from ideal-power cohomology

The generic site theorem retains the ideal-power short rows and the exact cohomological degree in
its public surface.  Its topological-space specialization is the source-facing form of Stacks
Lemma 20.35.3.
-/

@[expose] public section

open CategoryTheory.Limits Opposite
open CategoryTheory.PNatInverseSystem.IdealPower

noncomputable section

universe u v w

namespace CategoryTheory.SiteModuleCohomology.IdealPower

namespace Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/-- On an arbitrary site, a presented ideal-power quotient tower whose graded cohomology action
is induced by its multiplication diagrams has limit topology equal to its adic topology whenever
the exact-degree cohomology direct sum is Noetherian. -/
@[stacks 0GYM "site-level adic topology criterion for ideal-power cohomology"]
theorem limitTopology_eq_adic_of_isNoetherian
    (I : Ideal A)
    (F : PNatInverseSystem (Sheaf J (ModuleCat A)))
    (P : Presentation I F) (p : ℕ)
    [Action P p]
    [IsNoetherian (Ideal.AssociatedGraded.ring I)
      (SiteModuleCohomology.directSum (terms P) p)] :
    Functor.limitTopology
        (siteModuleCohomologyModuleTower F.toSequential p) =
      Ideal.adicModuleTopology I
        (limit (siteModuleCohomologyModuleTower F.toSequential p) : ModuleCat A) := sorry

end Site

section TopologicalSpace

variable {T : TopCat.{u}} {A : Type u} [CommRing A]
variable [HasWeakSheafify (_root_.Opens.grothendieckTopology T) (ModuleCat.{u} A)]
variable [HasSheafify (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (_root_.Opens.grothendieckTopology T) AddCommGrpCat.{u})]
variable [(_root_.Opens.grothendieckTopology T).HasSheafCompose
  (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u})]

/-- Lemma 20.35.3 (0GYM): let `F` be a positive tower and let `P` present each row as the
ideal-power quotient `F n = F (n + 1) / (I ^ n • F (n + 1))`. If the direct sum of the degree-`p`
cohomology of `F 1` in degree zero and the positive ideal-power terms is Noetherian for the graded
`gr_I(A)`-action induced by the installed multiplication diagrams, then the limit topology on
`lim n, H^p(T, F n)` is the
`I`-adic topology. -/
@[stacks 0GYM]
theorem limitTopology_eq_adic_of_isNoetherian
    (I : Ideal A)
    (F : PNatInverseSystem
      (Sheaf (_root_.Opens.grothendieckTopology T) (ModuleCat A)))
    (P : Presentation I F) (p : ℕ)
    [Action P p]
    [IsNoetherian (Ideal.AssociatedGraded.ring I)
      (SiteModuleCohomology.directSum (terms P) p)] :
    Functor.limitTopology
        (siteModuleCohomologyModuleTower F.toSequential p) =
      Ideal.adicModuleTopology I
        (limit (siteModuleCohomologyModuleTower F.toSequential p) : ModuleCat A) := sorry

end TopologicalSpace

end CategoryTheory.SiteModuleCohomology.IdealPower
