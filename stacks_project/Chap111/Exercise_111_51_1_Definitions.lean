/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.Genus
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (L : X.Modules)

/- Exercise 111.51.1 (Definitions) (1): `X` is a scheme. -/
@[stacks 02FG] #check Scheme

/- Exercise 111.51.1 (Definitions) (2): the morphism of schemes `f : X ⟶ Y` is finite. -/
@[stacks 02FG] #check (AlgebraicGeometry.IsFinite f : Prop)

#check (AlgebraicGeometry.isFinite_iff f :
  AlgebraicGeometry.IsFinite f ↔
    AlgebraicGeometry.IsAffineHom f ∧
      ∀ U : Y.Opens, AlgebraicGeometry.IsAffineOpen U → (f.app U).hom.Finite)

/- Exercise 111.51.1 (Definitions) (3): the morphism of schemes `f : X ⟶ Y` is of finite type. -/
@[stacks 02FG] #check (Scheme.Hom.FiniteType f : Prop)

#check (Scheme.Hom.finiteType_iff f :
  Scheme.Hom.FiniteType f ↔
    AlgebraicGeometry.QuasiCompact f ∧ AlgebraicGeometry.LocallyOfFiniteType f)

/- Exercise 111.51.1 (Definitions) (4): the scheme `X` is Noetherian. -/
@[stacks 02FG] #check (AlgebraicGeometry.IsNoetherian X : Prop)

#check (AlgebraicGeometry.isNoetherian_iff (X := X) :
  AlgebraicGeometry.IsNoetherian X ↔
    AlgebraicGeometry.IsLocallyNoetherian X ∧ CompactSpace X)

/- Exercise 111.51.1 (Definitions) (5): the `𝒪_X`-module `L` on the scheme `X` is invertible. -/
@[stacks 02FG] #check (Scheme.Modules.Invertible L : Prop)

/- Exercise 111.51.1 (Definitions) (6): the genus of a nonsingular projective curve over an
algebraically closed field. Over an algebraically closed field, a nonsingular projective curve
is a `Smooth` `Projective` `Curve`; geometric irreducibility is automatic for irreducible
curves. -/
@[stacks 02FG]
#check
  (AlgebraicGeometry.Curve.genus :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom], ℕ)

#check
  (AlgebraicGeometry.Curve.genus_def :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Curve X]
      [Projective X.hom] [Smooth X.hom] [GeometricallyIrreducible X.hom],
      AlgebraicGeometry.Curve.genus X =
        Scheme.Hom.cohomologyFinrank X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)
