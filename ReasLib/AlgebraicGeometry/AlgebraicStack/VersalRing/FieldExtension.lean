module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.VersalRing
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Restriction
public import ReasLib.AlgebraicGeometry.CompleteLocalAlgebra.ResidueExtension
public import ReasLib.RingTheory.Smooth.Adic.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Extension of versal rings along finite field extensions

A versal ring at a finite-type field-valued point of an algebraic stack
extends along a finite field extension through a map formally smooth for
the target maximal-adic topology and inducing the specified residue extension.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Let `X` be an algebraic stack locally of finite type over a locally Noetherian
scheme `S`, and let `x0 : Spec(k) ⟶ X` be a field-valued point locally of finite
type over `S`. Let `l / k` be a finite extension of
fields and denote `x0.restrict l : Spec(l) ⟶ X` the induced morphism. Given a
versal ring `A` to `X` at `x0` there exists a versal ring `A'` to `X` at
`x0.restrict l` such that there is an `S`-algebra map `A → A'` which induces
the given field extension `l / k` and is formally smooth in the
`m_{A'}`-adic topology. -/
@[stacks 0DQY]
theorem exists_isVersalRing_restrict {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} [AlgebraicStack X]
    [AlgebraicStack.LocallyOfFiniteType (baseProjection.{u + 1, u, u + 1} X)]
    (x0 : FieldValuedPoint X)
    [AlgebraicGeometry.LocallyOfFiniteType x0.structureHom]
    (l : Type u) [Field l] [Algebra x0.K l] [Module.Finite x0.K l]
    (A : CompleteLocalSAlgebra S) [IsVersalRing x0 A] :
    ∃ A' : CompleteLocalSAlgebra S,
      IsVersalRing (x0.restrict l) A' ∧
        ∃ φ : CompleteLocalSAlgebra.Hom A' A,
          φ.hom.formally_smooth_for_adic (maximalIdeal A'.carrier) ∧
            φ.InducesResidueExtension x0.K l x0.structureHom
              (x0.restrict l).structureHom :=
  sorry

end AlgebraicGeometry.AlgebraicStack
