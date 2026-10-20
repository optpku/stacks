/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
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

/- (1): `X` is a scheme. -/
#check (Scheme.{u} : Type (u + 1))

/- (2): the morphism of schemes `f : X ⟶ Y` is finite. -/
#check (AlgebraicGeometry.IsFinite f : Prop)

#check (AlgebraicGeometry.isFinite_iff f :
  AlgebraicGeometry.IsFinite f ↔
    AlgebraicGeometry.IsAffineHom f ∧
      ∀ U : Y.Opens, AlgebraicGeometry.IsAffineOpen U → (f.app U).hom.Finite)

/- (3): the morphism of schemes `f : X ⟶ Y` is of finite type. -/
#check (Scheme.Hom.FiniteType f : Prop)

#check (Scheme.Hom.finiteType_iff f :
  Scheme.Hom.FiniteType f ↔
    AlgebraicGeometry.QuasiCompact f ∧ AlgebraicGeometry.LocallyOfFiniteType f)

/- (4): the scheme `X` is Noetherian. -/
#check (AlgebraicGeometry.IsNoetherian X : Prop)

#check (AlgebraicGeometry.isNoetherian_iff (X := X) :
  AlgebraicGeometry.IsNoetherian X ↔
    AlgebraicGeometry.IsLocallyNoetherian X ∧ CompactSpace X)

/- (5): the `𝒪_X`-module `L` on the scheme `X` is invertible. -/
#check (Scheme.Modules.Invertible L : Prop)

/- Exercise 111.51.1 (Definitions)
Define schemes, finite and finite-type scheme morphisms, Noetherian schemes, invertible
module sheaves, and the genus of a nonsingular projective curve over an algebraically
closed field. The checks above give definitions (1)–(5).
(6): The genus is the degree-one structure-sheaf cohomology dimension of a `Smooth`
`Projective` `Curve` over an algebraically closed field. -/
@[stacks 02FG]
#check
  (AlgebraicGeometry.Curve.genusOfAlgClosed :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Curve X]
      [Projective X.hom] [Smooth X.hom], ℕ)

#check
  (AlgebraicGeometry.Curve.genusOfAlgClosed_def :
    ∀ {k : Type u} [Field k] [IsAlgClosed k] (X : SchemeOverField k) [Curve X]
      [Projective X.hom] [Smooth X.hom],
      AlgebraicGeometry.Curve.genusOfAlgClosed X =
        Scheme.Hom.cohomologyFinrank X.hom
          (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)

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
