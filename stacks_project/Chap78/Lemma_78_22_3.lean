/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf
public import stacks_project.Chap78.Definition_78_19_1_QuotientSheaf
public import stacks_project.Chap78.Lemma_78_22_1_Isom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.LocalRepresentability
import StacksCheckRecall

/-!
# Local algebraic-space representability of Isom sheaves on a quotient stack

This file records that the Hom sheaf `Isom(x, y)` of `[U/R]` on `(Sch/T)_fppf` is
fppf-locally isomorphic to the universe-raised sheaf of points of an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace GroupoidAlgebraicSpace

noncomputable section

universe u

/- Lemma 78.22.3. Assume `B → S` and `(U, R, s, t, c)` are as in Definition 78.20.1 (1). For any
scheme `T` over `S` and objects `x, y` of `[U/R]` over `T`, the sheaf `Isom(x, y)` on
`(Sch/T)_fppf` is fppf-locally representable by an algebraic space: there exists an fppf covering
`{T_i → T}` such that each restriction `Isom(x, y)|_{(Sch/T_i)_fppf}` is isomorphic to the
universe-raised sheaf of points of an algebraic space over `T_i`. -/
@[stacks 044W]
#check (AlgebraicGeometry.GroupoidAlgebraicSpace.sheafHom_locally_representableByAlgebraicSpace :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (x y : (fppfQuotientStack G).p.Fiber T),
    ∃ (ι : Type u) (𝒯 : ι → Over T.left),
      Scheme.FppfCovering 𝒯 ∧
        ∀ i, ∃ (M : AlgebraicSpace (𝒯 i).left),
          Nonempty
            (AlgebraicSpace.toSheaf.obj M ≅
              (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (𝒯 i).hom).obj
                (sheafHomOverLeft G x y)))
