module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.ResidueField
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ResidueField

/-!
# Residue-field extension conditions for scheme morphisms

This leaf contains pointwise finiteness and algebraicity conditions on the
residue-field extensions induced by scheme morphisms.  It is independent of
finite-type, flatness, and fibre-dimension arguments that use these
conditions.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

namespace ResidueField

/-- The residue-field extension induced by `f` at `x` is finite. -/
def finiteAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  let _ : Algebra (Y.residueField (f x)) (X.residueField x) := residueFieldAlgebra f x
  Module.Finite (Y.residueField (f x)) (X.residueField x)

/-- The residue-field extension induced by `f` at `x` is algebraic. -/
def algebraicAt {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : Prop :=
  let _ : Algebra (Y.residueField (f x)) (X.residueField x) := residueFieldAlgebra f x
  Algebra.IsAlgebraic (Y.residueField (f x)) (X.residueField x)

end ResidueField

/-- The image in a target scheme of the unique closed point of a field-valued
point. -/
abbrev closedPointImage {T : Scheme.{u}} {k : Type u} [Field k]
    (f : Spec (CommRingCat.of k) ⟶ T) : T :=
  f (IsLocalRing.closedPoint k)

/-- The canonical algebra structure on the source field over the residue field
of the image of a field-valued point. -/
noncomputable instance closedPointImageResidueFieldAlgebra
    {T : Scheme.{u}} {k : Type u} [Field k]
    (f : Spec (CommRingCat.of k) ⟶ T) :
    Algebra (T.residueField (closedPointImage f)) k :=
  (CommRingCat.Hom.hom
    (Scheme.descResidueField (Scheme.stalkClosedPointTo f))).toAlgebra

/-- A field-valued point has finite residue-field extension when its source
field is finite over the residue field at the image of its closed point. -/
def HasFiniteResidueFieldExtension {T : Scheme.{u}} {k : Type u} [Field k]
    (f : Spec (CommRingCat.of k) ⟶ T) : Prop :=
  Module.Finite (T.residueField (closedPointImage f)) k

/-- Unfold finite residue-field extension for a field-valued point. -/
theorem hasFiniteResidueFieldExtension_iff {T : Scheme.{u}} {k : Type u} [Field k]
    (f : Spec (CommRingCat.of k) ⟶ T) :
    HasFiniteResidueFieldExtension f ↔
      Module.Finite (T.residueField (closedPointImage f)) k :=
  Iff.rfl

/-- A scheme morphism has algebraic residue-field extensions when every map
`κ(g(s')) → κ(s')` is algebraic. -/
def HasAlgebraicResidueFieldExtensions {S S' : Scheme.{u}}
    (g : S' ⟶ S) : Prop :=
  ∀ s' : S',
    let _ : Algebra (S.residueField (g s')) (S'.residueField s') :=
      residueFieldAlgebra g s'
    Algebra.IsAlgebraic (S.residueField (g s')) (S'.residueField s')

/-- Unfold algebraicity of all residue-field extensions induced by a scheme
morphism. -/
theorem hasAlgebraicResidueFieldExtensions_iff {S S' : Scheme.{u}}
    (g : S' ⟶ S) :
    HasAlgebraicResidueFieldExtensions g ↔
      ∀ s' : S',
        let _ : Algebra (S.residueField (g s')) (S'.residueField s') :=
          residueFieldAlgebra g s'
        Algebra.IsAlgebraic (S.residueField (g s')) (S'.residueField s') :=
  Iff.rfl

/-- A locally quasi-finite scheme morphism has algebraic residue-field
extensions. -/
theorem hasAlgebraicResidueFieldExtensions_of_locallyQuasiFinite
    {S S' : Scheme.{u}} (g : S' ⟶ S) [LocallyQuasiFinite g] :
    HasAlgebraicResidueFieldExtensions g := sorry

end AlgebraicGeometry.Scheme.Hom
