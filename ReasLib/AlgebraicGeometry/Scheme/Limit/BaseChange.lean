/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-!
# Base change of diagrams of schemes

This leaf constructs the diagram obtained by base changing all stages over a
fixed object of an arbitrary diagram, and the cone induced from a cone on the
original diagram.  For a cofiltered-or-empty index category, the induced cone
is limiting whenever the original cone is limiting.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- The diagram of base changes `T ×_{D(i₀)} D(j)` indexed by objects of
`Over i₀`. -/
noncomputable def baseChangeOverDiagram {C : Type u} [Category C]
    (D : C ⥤ Scheme.{u}) (i₀ : C) {T : Scheme.{u}} (t : T ⟶ D.obj i₀) :
    Over i₀ ⥤ Scheme.{u} :=
  Over.post D ⋙ Over.pullback t ⋙ Over.forget _

/-- The cone on `baseChangeOverDiagram D i₀ t` induced by a cone on `D`. -/
noncomputable def baseChangeOverCone {C : Type u} [Category C]
    (D : C ⥤ Scheme.{u}) (c : Cone D) (i₀ : C) {T : Scheme.{u}}
    (t : T ⟶ D.obj i₀) :
    Cone (baseChangeOverDiagram D i₀ t) :=
  (Over.pullback t ⋙ Over.forget _).mapCone ((Over.conePost D i₀).obj c)

/-- Base change over a fixed object carries a limiting cone indexed by a
cofiltered-or-empty category to a limiting cone on the corresponding slice. -/
noncomputable def isLimitBaseChangeOverCone {C : Type u} [Category C]
    [IsCofilteredOrEmpty C] (D : C ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    (i₀ : C) {T : Scheme.{u}} (t : T ⟶ D.obj i₀) :
    IsLimit (baseChangeOverCone D c i₀ t) := by
  -- Local instance justification (proof-local temporary data): enables connected-limit preservation for `Over.forget` on `Over i₀`.
  letI : IsConnected (Over i₀) := IsCofiltered.isConnected (Over i₀)
  exact isLimitOfPreserves (Over.pullback t ⋙ Over.forget _) (Over.isLimitConePost i₀ hc)

/-- If the base change of a quasi-compact scheme to the limit of a directed
inverse system with affine transition maps is empty, then its base changes are
empty at every stage beyond some threshold. -/
theorem exists_eventually_isEmpty_baseChangeOverDiagram
    {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
    (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
    [∀ j, CompactSpace (D.obj j)]
    [∀ {j k : OrderDual I} (f : j ⟶ k), IsAffineHom (D.map f)]
    (i : I) [QuasiSeparatedSpace (D.obj i)] {T : Scheme.{u}}
    (t : T ⟶ D.obj i) [CompactSpace T]
    (hempty : IsEmpty (baseChangeOverCone D c i t).pt) :
    ∃ (i₀ : I) (hii₀ : i ≤ i₀), ∀ ⦃i' : I⦄, (hi₀i' : i₀ ≤ i') →
      IsEmpty ((baseChangeOverDiagram D i t).obj
        (Over.mk (homOfLE ((le_trans hii₀ hi₀i' : i ≤ i') :
          OrderDual.toDual i' ≤ OrderDual.toDual i)))) := sorry

end AlgebraicGeometry.Scheme
