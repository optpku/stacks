/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

variable {S : Scheme.{u}} {H : (Over S)ᵒᵖ ⥤ Type u} {F G : AlgebraicSpace S}
variable (f : F.functorOfPoints ⟶ H) (g : G.functorOfPoints ⟶ H)
variable (hH : Presheaf.IsSheaf (Scheme.fppfTopology.over S) H)
variable (hΔ : yoneda.relativelyRepresentable (Limits.diag H))

/- Lemma 65.7.2: let `S` be a scheme contained in `Sch_fppf`. Let `H` be a sheaf
on `(Sch/S)_fppf` whose diagonal is representable. Let `F`, `G` be algebraic
spaces over `S`. Let `F ⟶ H`, `G ⟶ H` be maps of sheaves. Then `F ×_H G` is an
algebraic space. -/
@[stacks 04T9] #check
  (AlgebraicGeometry.AlgebraicSpace.ReasLibPullback.pullbackOver f g hH hΔ : AlgebraicSpace S)
