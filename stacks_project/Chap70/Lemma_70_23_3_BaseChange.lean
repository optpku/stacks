/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import stacks_project.Chap65.Lemma_65_7_3_Pullback

/-!
# Base change of diagrams of algebraic spaces

The diagram of fibre products `T ×_{D(i₀)} D(j)` indexed by `Over i₀`, and the
cone induced from a cone on the original diagram.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The diagram of base changes `T ×_{D(i₀)} D(j)` indexed by objects of
`Over i₀`. -/
noncomputable def baseChangeOverDiagram {C : Type u} [Category C]
    {S : Scheme.{u}} (D : C ⥤ AlgebraicSpace S) (i₀ : C)
    {T : AlgebraicSpace S} (t : T ⟶ D.obj i₀) :
    Over i₀ ⥤ AlgebraicSpace S :=
  Over.post D ⋙ Over.pullback t ⋙ Over.forget T

/-- The value of `baseChangeOverDiagram D i₀ t` at `Over.mk g` is the pullback of
`t` along `D.map g`. -/
theorem baseChangeOverDiagram_obj {C : Type u} [Category C] {S : Scheme.{u}}
    (D : C ⥤ AlgebraicSpace S) (i₀ : C) {T : AlgebraicSpace S}
    (t : T ⟶ D.obj i₀) {j : C} (g : j ⟶ i₀) :
    (baseChangeOverDiagram D i₀ t).obj (Over.mk g) = pullback (D.map g) t :=
  sorry

/-- The cone on `baseChangeOverDiagram D i₀ t` induced by a cone on `D`. -/
noncomputable def baseChangeOverCone {C : Type u} [Category C]
    {S : Scheme.{u}} (D : C ⥤ AlgebraicSpace S) (c : Cone D) (i₀ : C)
    {T : AlgebraicSpace S} (t : T ⟶ D.obj i₀) :
    Cone (baseChangeOverDiagram D i₀ t) :=
  (Over.pullback t ⋙ Over.forget T).mapCone ((Over.conePost D i₀).obj c)

/-- The vertex of `baseChangeOverCone D c i₀ t` is the pullback of `t` along the
cone leg at `i₀`. -/
theorem baseChangeOverCone_pt {C : Type u} [Category C] {S : Scheme.{u}}
    (D : C ⥤ AlgebraicSpace S) (c : Cone D) (i₀ : C)
    {T : AlgebraicSpace S} (t : T ⟶ D.obj i₀) :
    (baseChangeOverCone D c i₀ t).pt = pullback (c.π.app i₀) t :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
