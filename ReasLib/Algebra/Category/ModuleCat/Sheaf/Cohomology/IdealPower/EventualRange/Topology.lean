/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Cohomology.IdealPower.EventualRange
public import ReasLib.RingTheory.Topology.Adic.InverseLimit
import Mathlib.Tactic.CrossRefAttribute

/-!
# Adic topology from stable ideal-power cohomology

This leaf is the stable-image analogue of the diagonal ideal-power topology criterion.  Its
Noetherian source is the exact-degree direct sum `⨁ n, N n`; comparison maps to the intrinsic
associated graded of the inverse limit remain proof infrastructure and are not public inputs.
-/

@[expose] public section

open CategoryTheory.Limits Opposite
open CategoryTheory.PNatInverseSystem.IdealPower

noncomputable section

universe u v w

namespace CategoryTheory.SiteModuleCohomology.IdealPower.Eventual

namespace Site

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {A : Type w} [CommRing A]
variable [HasWeakSheafify J (ModuleCat.{max u v w} A)]
variable [HasSheafify J AddCommGrpCat.{max u v w}]
variable [HasExt (Sheaf J AddCommGrpCat.{max u v w})]
variable [J.HasSheafCompose
  (forget₂ (ModuleCat.{max u v w} A) AddCommGrpCat.{max u v w})]

/-- On an arbitrary site, Noetherianity of the canonically acted-on exact-degree stable
ideal-power cohomology direct sum identifies the inverse-limit topology with the adic topology. -/
@[stacks 0GYN "site-level adic topology criterion for stable ideal-power cohomology"]
theorem limitTopology_eq_adic_of_isNoetherian
    (I : Ideal A)
    (F : PNatInverseSystem (Sheaf J (ModuleCat A)))
    (P : PNatInverseSystem.IdealPower.Family I F)
    (p : ℕ) [Action P p]
    [IsNoetherian (Ideal.AssociatedGraded.ring I) (directSum P p)] :
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

/-- Lemma 20.35.4 (0GYN): let `P` present the two-parameter family
`I ^ n • F (m + 1)` and let `N n` be the stable image of its exact degree-`p` cohomology at
stage `n`.  If `⨁ n, N n` is Noetherian for its canonical graded `gr_I(A)`-action, then the
limit topology on `lim n, H^p(T, F n)` is the `I`-adic topology. -/
@[stacks 0GYN]
theorem limitTopology_eq_adic_of_isNoetherian
    (I : Ideal A)
    (F : PNatInverseSystem
      (Sheaf (_root_.Opens.grothendieckTopology T) (ModuleCat A)))
    (P : PNatInverseSystem.IdealPower.Family I F)
    (p : ℕ) [Action P p]
    [IsNoetherian (Ideal.AssociatedGraded.ring I) (directSum P p)] :
    Functor.limitTopology
        (siteModuleCohomologyModuleTower F.toSequential p) =
      Ideal.adicModuleTopology I
        (limit (siteModuleCohomologyModuleTower F.toSequential p) : ModuleCat A) := sorry

end TopologicalSpace

end CategoryTheory.SiteModuleCohomology.IdealPower.Eventual
