/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicStack.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicStack.LocallyOfFinitePresentation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.TwoFibreProduct

/-!
# Flat and unramified characterizations of étale morphisms of algebraic stacks

A morphism of algebraic stacks is étale if and only if it is locally of finite
presentation, flat, and unramified, equivalently if and only if it is locally
of finite presentation, flat, and its relative 2-diagonal is étale.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack.Etale

variable {S : Scheme.{u}} {X Y : GroupoidsOver S}
variable [AlgebraicStack X] [AlgebraicStack Y]

/-- For a morphism of algebraic stacks, being étale is equivalent to being
locally of finite presentation, flat, and unramified, and to being locally of
finite presentation and flat with étale relative 2-diagonal. -/
theorem tfae_flat_unramified (f : X ⟶ Y) :
    List.TFAE
      [Etale f,
        LocallyOfFinitePresentation f ∧ Flat f ∧ Unramified f,
        LocallyOfFinitePresentation f ∧
          Flat f ∧ Etale (Hom.diagonal.{u + 1, u, u + 1} f)] :=
  sorry

/-- A morphism of algebraic stacks is étale if and only if it is locally of
finite presentation, flat, and unramified. -/
theorem iff_locallyOfFinitePresentation_flat_unramified (f : X ⟶ Y) :
    Etale f ↔ LocallyOfFinitePresentation f ∧ Flat f ∧ Unramified f :=
  (tfae_flat_unramified f).out 0 1

/-- A morphism of algebraic stacks is étale if and only if it is locally of
finite presentation, flat, and its relative 2-diagonal is étale. -/
theorem iff_locallyOfFinitePresentation_flat_etale_diagonal (f : X ⟶ Y) :
    Etale f ↔
      LocallyOfFinitePresentation f ∧
        Flat f ∧ Etale (Hom.diagonal.{u + 1, u, u + 1} f) :=
  (tfae_flat_unramified f).out 0 2

/-- An étale morphism of algebraic stacks is locally of finite presentation. -/
instance locallyOfFinitePresentation (f : X ⟶ Y) [hf : Etale f] :
    LocallyOfFinitePresentation f :=
  ((iff_locallyOfFinitePresentation_flat_unramified f).mp hf).1

/-- An étale morphism of algebraic stacks is flat. -/
instance flat (f : X ⟶ Y) [hf : Etale f] :
    Flat f :=
  ((iff_locallyOfFinitePresentation_flat_unramified f).mp hf).2.1

/-- A locally of finite presentation, flat, unramified morphism of algebraic
stacks is étale. -/
@[instance 900]
instance of_locallyOfFinitePresentation_of_flat_of_unramified (f : X ⟶ Y)
    [hlfp : LocallyOfFinitePresentation f] [hflat : Flat f] [hunr : Unramified f] :
    Etale f :=
  (iff_locallyOfFinitePresentation_flat_unramified f).mpr ⟨hlfp, hflat, hunr⟩

/-- A locally of finite presentation, flat morphism of algebraic stacks whose
relative 2-diagonal is étale is étale. -/
theorem of_locallyOfFinitePresentation_of_flat_of_etale_diagonal (f : X ⟶ Y)
    [hlfp : LocallyOfFinitePresentation f] [hflat : Flat f]
    [hdiag : Etale (Hom.diagonal.{u + 1, u, u + 1} f)] :
    Etale f :=
  (iff_locallyOfFinitePresentation_flat_etale_diagonal f).mpr ⟨hlfp, hflat, hdiag⟩

end AlgebraicGeometry.AlgebraicStack.Etale
