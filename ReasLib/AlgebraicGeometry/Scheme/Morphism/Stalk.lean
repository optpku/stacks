module

public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Stalk algebras of scheme morphisms

This leaf owns the algebra structure on source stalks induced by a scheme morphism, together with
its specialization to morphisms into `Spec k` without packaging the scheme as an object over
`Spec k`.
-/

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- The local ring of a scheme at a point acts canonically on its residue field. -/
noncomputable instance residueFieldAlgebra {X : Scheme.{u}} (x : X) :
    Algebra (X.presheaf.stalk x) (X.residueField x) :=
  (X.residue x).hom.toAlgebra

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.Hom

/-- A scheme morphism induces an algebra structure on the source stalk over the target stalk. -/
noncomputable abbrev stalkAlgebra {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

variable {k : Type u} [Field k]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))

/-- A morphism `f : X ⟶ Spec k` induces the canonical `k`-algebra structure on the local ring at
each point of `X`. -/
@[stacks 035V]
noncomputable abbrev stalkAlgebraOverField (x : X) :
    Algebra k (X.presheaf.stalk x) :=
  (CommRingCat.Hom.hom <|
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        Scheme.Hom.appTop (X.fromSpecStalk x ≫ f) ≫
        (Scheme.ΓSpecIso (CommRingCat.of (X.presheaf.stalk x))).hom).toAlgebra

/-- The local ring at a point, bundled as a commutative `k`-algebra through `f`. -/
@[stacks 035V "bundled stalk algebra over a field"]
noncomputable def stalkAlgOverField (x : X) : CommAlgCat k :=
  @CommAlgCat.of k _ (X.presheaf.stalk x) _ (stalkAlgebraOverField f x)

end AlgebraicGeometry.Scheme.Hom
