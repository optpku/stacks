/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap94.Definition_94_12_1_Representable
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory CategoryTheory.TwoFibreProduct

universe u

section
variable {S : Scheme.{u}} {HXY HX'Y : GroupoidsOver S} (φ : HX'Y ⟶ HXY)
variable {U : Over S} (ξ : GroupoidsOver.slice U ⟶ HXY)

/- 97.12.3.1: the displayed 2-fibre product
`(Sch/U)_fppf ×_{ξ, ℋ_d(𝒳/𝒴)} ℋ_d(𝒳'/𝒴)` is
`TwoFibreProduct.apex ξ φ` in `GroupoidsOver S`.
Here `HXY` stands for `ℋ_d(𝒳/𝒴)`, `HX'Y` for `ℋ_d(𝒳'/𝒴)`,
`GroupoidsOver.slice U` is `(Sch/U)_fppf`, `ξ` is the 2-Yoneda 1-morphism
of an object of `ℋ_d(𝒳/𝒴)` over `U`, and `φ` is the canonical 1-morphism
`ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of lemma-map-hilbert. -/
@[stacks 05XT]
#check (TwoFibreProduct.apex.{u + 1, u, u + 1, u} ξ φ)
end
