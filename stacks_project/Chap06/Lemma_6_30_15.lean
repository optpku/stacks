/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Basis.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {X Y : RingedSpace.{u}} (f : X ⟶ Y)
variable {B : Set (Opens Y)} (hB : Opens.IsBasis B)
variable (ℱ : SheafOfModules (RingedSpace.ringCatSheaf X))
variable (𝒢 : SheafOfModules (RingedSpace.ringCatSheaf Y))

/- Lemma 6.30.15: let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces, let `ℱ`
be a sheaf of `𝒪_X`-modules, let `𝒢` be a sheaf of `𝒪_Y`-modules, and let `B` be a basis of `Y`.
A morphism between the restrictions of `𝒢` and `f_* ℱ` to the basis site attached to `B` extends
uniquely to a global morphism `𝒢 ⟶ f_* ℱ`; equivalently, a compatible family of
`𝒪_Y(V)`-linear maps `𝒢(V) ⟶ ℱ(f⁻¹(V))` for `V ∈ B` comes from a unique `f`-map. -/
@[stacks 009W]
#check
  BasisSiteSheaf.moduleRestrictionHomEquiv hB 𝒢 ((f _*).obj ℱ)

end

end AlgebraicGeometry
