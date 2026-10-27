/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Smooth
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Small
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Saturation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.LocallyOfFinitePresentation
public import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Algebraicity of groupoid quotients

The quotient stack of a smooth groupoid in algebraic spaces is an algebraic stack.
More generally, algebraicity is characterized by a restriction with locally
surjective saturation morphism and flat, locally finitely presented structure maps.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The quotient stack of a smooth groupoid in algebraic spaces over an algebraic
space over a scheme `S` is an algebraic stack over `S`. -/
theorem instAlgebraicStack_quotientStack {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) [Smooth G] :
    AlgebraicStack (SmallQuotient.quotientStack G) :=
  sorry

/-- A groupoid in algebraic spaces with flat, locally finitely presented source
and target maps has an algebraic quotient stack. -/
theorem isAlgebraicStack_quotientStack_of_flat {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) (h_flat : Flat G)
    (h_lfp : LocallyOfFinitePresentation G) :
    AlgebraicStack (SmallQuotient.quotientStack G) := sorry

/-- The quotient stack of a groupoid in algebraic spaces is algebraic if and only if
some restriction has fppf-locally-surjective saturation morphism and flat, locally
finitely presented source and target maps. -/
theorem isAlgebraicStack_quotientStack_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) :
    AlgebraicStack (SmallQuotient.quotientStack G) ↔
      ∃ (U' : Over B) (g : U' ⟶ G.U),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (G.saturationMap g).left ∧
          Flat (G.pullback g) ∧ LocallyOfFinitePresentation (G.pullback g) := sorry

/-- If a restriction has fppf-locally-surjective saturation morphism and flat,
locally finitely presented source and target maps, the original quotient stack
is algebraic. -/
theorem isAlgebraicStack_quotientStack_of_pullback {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) {U' : Over B}
    (g : U' ⟶ G.U)
    (h_sat : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (G.saturationMap g).left)
    [Flat (G.pullback g)] [LocallyOfFinitePresentation (G.pullback g)] :
    AlgebraicStack (SmallQuotient.quotientStack G) := sorry

/-- An algebraic quotient stack admits a restriction with fppf-locally-surjective
saturation morphism and flat, locally finitely presented source and target maps. -/
theorem exists_pullback_of_isAlgebraicStack_quotientStack {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    [AlgebraicStack (SmallQuotient.quotientStack G)] :
    ∃ (U' : Over B) (g : U' ⟶ G.U),
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
          (G.saturationMap g).left ∧
        Flat (G.pullback g) ∧ LocallyOfFinitePresentation (G.pullback g) := sorry

/-- The quotient stack is algebraic exactly when a restriction has
fppf-locally-surjective saturation morphism and each of its source and target maps
is flat and locally of finite presentation. -/
theorem isAlgebraicStack_quotientStack_iff_spec {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B) :
    AlgebraicStack (SmallQuotient.quotientStack G) ↔
      ∃ (U' : Over B) (g : U' ⟶ G.U),
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (G.saturationMap g).left ∧
          AlgebraicSpace.Flat (G.pullback g).s.left ∧
            AlgebraicSpace.Flat (G.pullback g).t.left ∧
              AlgebraicSpace.LocallyOfFinitePresentation (G.pullback g).s.left ∧
                AlgebraicSpace.LocallyOfFinitePresentation
                  (G.pullback g).t.left := sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
