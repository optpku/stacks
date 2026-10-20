/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Quotient.Isom
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Cover.Fppf

/-!
# Local representability of quotient-stack Hom sheaves

The Hom sheaf between two objects of an fppf quotient stack is fppf-locally
representable by an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidAlgebraicSpace

/-- The Hom sheaf between two objects of the fppf quotient stack, transported along the
iterated-slice equivalence to the fppf site of schemes over their base. -/
def sheafHomOverLeft {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (x y : (fppfQuotientStack G).p.Fiber T) :
    Sheaf (Scheme.fppfTopology.over T.left) (Type (u + 1)) :=
  (T.iteratedSliceEquiv.sheafCongr ((Scheme.fppfTopology.over S).over T)
    (Scheme.fppfTopology.over T.left) (Type (u + 1))).functor.obj
      ((Functor.fiberPseudofunctor (fppfQuotientStack G).p).sheafHom
        (Scheme.fppfTopology.over S) x y)

/-- The underlying presheaf of the transported Hom sheaf is obtained by precomposing
the quotient-stack Hom sheaf with the inverse iterated-slice equivalence. -/
theorem sheafHomOverLeft_obj {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupoidAlgebraicSpace B) {T : Over S} (x y : (fppfQuotientStack G).p.Fiber T) :
    (sheafHomOverLeft G x y).obj =
      T.iteratedSliceEquiv.inverse.op ⋙
        ((Functor.fiberPseudofunctor (fppfQuotientStack G).p).sheafHom
          (Scheme.fppfTopology.over S) x y).obj :=
  rfl

/-- The Hom sheaf between any two objects of an fppf quotient stack becomes representable
by an algebraic space after an fppf covering of the base scheme. -/
theorem sheafHom_locally_representableByAlgebraicSpace
    {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupoidAlgebraicSpace B)
    {T : Over S} (x y : (fppfQuotientStack G).p.Fiber T) :
    ∃ (ι : Type u) (𝒯 : ι → Over T.left),
      Scheme.FppfCovering 𝒯 ∧
        ∀ i, ∃ (M : AlgebraicSpace (𝒯 i).left),
          Nonempty
            (AlgebraicSpace.toSheaf.obj M ≅
              (Scheme.fppfTopology.overMapPullback (Type (u + 1)) (𝒯 i).hom).obj
                (sheafHomOverLeft G x y)) :=
  sorry

end AlgebraicGeometry.GroupoidAlgebraicSpace
