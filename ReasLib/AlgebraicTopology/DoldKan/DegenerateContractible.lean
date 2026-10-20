/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.DoldKan.ProjectionHomotopy
public import ReasLib.AlgebraicTopology.DoldKan.DegenerateComplex.Projection
public import ReasLib.Algebra.Homology.Homotopy.Contractible
public import ReasLib.Algebra.Homology.Homotopy.Whisker

/-!
# Contractibility of the Dold--Kan degenerate complex

The complement-projector homotopy restricts to an explicit contraction of the degenerate
subcomplex. The construction only uses the limits and colimits needed to form that subcomplex;
it does not require an abelian category.

@stack 019C
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology HomologicalComplex
open scoped DoldKan

noncomputable section

universe v u

namespace AlgebraicTopology.DoldKan

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasBinaryCoproducts C] [HasImages C]

namespace degenerateComplex

namespace contraction

/-- The `Q∞` null-homotopy restricted to the degenerate retract. -/
@[stacks 019C "restricted null-homotopy on the degenerate retract"]
noncomputable def projector (U : SimplicialObject C) :
    Homotopy
      ((degenerateComplex.ι U ≫ (QInfty : K[U] ⟶ K[U])) ≫
        degenerateComplex.π U)
      ((degenerateComplex.ι U ≫ (0 : K[U] ⟶ K[U])) ≫
        degenerateComplex.π U) :=
  Homotopy.whisker (degenerateComplex.ι U) (QInfty.homotopyToZero U)
    (degenerateComplex.π U)

/-- The source of the restricted `Q∞` null-homotopy is the identity. -/
@[stacks 019C "source of the restricted projector homotopy"]
theorem projector.source (U : SimplicialObject C) :
    (degenerateComplex.ι U ≫ (QInfty : K[U] ⟶ K[U])) ≫
        degenerateComplex.π U =
      𝟙 D[U] := sorry

/-- The target of the restricted `Q∞` null-homotopy is zero. -/
@[stacks 019C "target of the restricted projector homotopy"]
theorem projector.target (U : SimplicialObject C) :
    (degenerateComplex.ι U ≫ (0 : K[U] ⟶ K[U])) ≫
        degenerateComplex.π U =
      0 := sorry

end contraction

/-- An explicit contraction of the degenerate complex. -/
@[stacks 019C "contractibility of the degenerate complex"]
noncomputable def contraction (U : SimplicialObject C) :
    Homotopy (𝟙 D[U]) (0 : D[U] ⟶ D[U]) :=
  Homotopy.trans
    (Homotopy.ofEq (contraction.projector.source U).symm)
    (Homotopy.trans (contraction.projector U)
      (Homotopy.ofEq (contraction.projector.target U)))

/-- The degenerate complex is contractible. -/
@[stacks 019C "contractibility of the degenerate complex"]
theorem contractible (U : SimplicialObject C) :
    D[U].Contractible := sorry

end degenerateComplex

end AlgebraicTopology.DoldKan

namespace AlgebraicTopology.DoldKan.QInfty

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable [HasImages (ChainComplex C ℕ)] [HasStrongEpiImages (ChainComplex C ℕ)]

namespace contraction

/-- The complement-projector null-homotopy restricted to the canonical image of `QInfty`. -/
@[stacks 019C "canonical QInfty image projector homotopy"]
noncomputable def projector (U : SimplicialObject C) :
    Homotopy
      ((QInfty.fromImage U ≫ (QInfty : K[U] ⟶ K[U])) ≫ QInfty.toImage U)
      ((QInfty.fromImage U ≫ (0 : K[U] ⟶ K[U])) ≫ QInfty.toImage U) :=
  Homotopy.whisker (QInfty.fromImage U) (QInfty.homotopyToZero U)
    (QInfty.toImage U)

/-- The restricted projector homotopy starts at the identity of the canonical image. -/
@[stacks 019C "canonical QInfty image projector homotopy source"]
theorem projector.source (U : SimplicialObject C) :
    ((QInfty.fromImage U ≫ (QInfty : K[U] ⟶ K[U])) ≫ QInfty.toImage U) =
      𝟙 (QInfty.image U) := sorry

/-- The restricted projector homotopy ends at the zero endomorphism. -/
@[stacks 019C "canonical QInfty image projector homotopy target"]
theorem projector.target (U : SimplicialObject C) :
    ((QInfty.fromImage U ≫ (0 : K[U] ⟶ K[U])) ≫ QInfty.toImage U) =
      0 := sorry

end contraction

/-- An explicit contraction of the canonical image of `QInfty`. -/
@[stacks 019C "canonical QInfty image contraction"]
noncomputable def contraction (U : SimplicialObject C) :
    Homotopy (𝟙 (QInfty.image U)) (0 : QInfty.image U ⟶ QInfty.image U) :=
  Homotopy.trans
    (Homotopy.ofEq (contraction.projector.source U).symm)
    (Homotopy.trans (contraction.projector U)
      (Homotopy.ofEq (contraction.projector.target U)))

/-- The canonical image of `QInfty` is contractible. -/
@[stacks 019C "contractibility of the canonical QInfty image"]
theorem contractible (U : SimplicialObject C) :
    (QInfty.image U).Contractible := sorry

end AlgebraicTopology.DoldKan.QInfty
