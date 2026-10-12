/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap85.Lemma_85_24_5_CoveringFamily

/-!
# Lemma 85.24.5

On a ringed site with fibre products, derived modules on the members of a
covering, together with cocycle isomorphisms, vanishing of negative self-Ext
sheaves, and a uniform lower bound on cohomology, glue uniquely up to a unique
compatible isomorphism.
-/

@[expose]
public section

open CategoryTheory CategoryTheory.Limits
open RingedSite RingedSite.Hom
open RingedSite.ModuleDerived

noncomputable section

universe ι u v w

namespace RingedSite.ModuleDerived.CoveringFamily

variable {C : RingedSite.{u, v, w}} {X : C}
variable [HasPullbacks C.carrier] [UnivLE.{max u v, w}]
variable {𝒰 : FormalCoproduct.{ι} (Over X)}
variable (G : CoveringFamily C X 𝒰)

/-- Lemma 85.24.5 (1)
Let `(C, O_C)` be a ringed site with fibre products, and let `{U_i ⟶ X}` be a
covering. Given objects `E_i` of `ModuleDerived (C.localization U_i)` and
cocycle isomorphisms `ρ_ij : E_i|_{U_ij} ≅ E_j|_{U_ij}` on
`U_ij = U_i ×_X U_j`, if the negative self-Ext sheaves of each `E_i` vanish and
the `E_i` are uniformly bounded below, then a solution exists. -/
@[stacks 0GMG]
theorem exists_solution (h_cover : 𝒰.toSieve ∈ C.siteTopology X)
    (h_neg : G.negativeSheafSelfExt) (h_bound : G.uniformlyBoundedBelow) :
    Nonempty (Solution G) :=
  sorry

/-- Lemma 85.24.5 (2)
In the situation of Lemma 85.24.5 (1), a solution is unique up to a unique
isomorphism of global objects compatible with the identifications `ρ_i`. -/
@[stacks 0GMG]
theorem unique_hom_solution (h_cover : 𝒰.toSieve ∈ C.siteTopology X)
    (h_neg : G.negativeSheafSelfExt) (h_bound : G.uniformlyBoundedBelow)
    (S S' : Solution G) :
    ∃ e : S.obj ≅ S'.obj,
      Solution.IsCompatibleIso S S' e ∧
        ∀ e' : S.obj ≅ S'.obj, Solution.IsCompatibleIso S S' e' →
          e'.hom = e.hom :=
  sorry

end RingedSite.ModuleDerived.CoveringFamily
