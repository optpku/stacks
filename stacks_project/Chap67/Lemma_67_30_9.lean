/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Flat
public import stacks_project.Chap66.Lemma_66_28_1_Hom
public import stacks_project.Chap67.Lemma_67_30_5_Flat

/-!
# Flat morphisms of algebraic spaces via the small étale site

A morphism of algebraic spaces is flat if and only if the associated morphism
of small étale ringed topoi is flat.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- Lemma 67.30.9: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of
algebraic spaces over `S`. Then `f` is flat if and only if the associated
morphism of small étale sites `(f_small, f^♯) : (X_étale, 𝒪_X) ⟶
(Y_étale, 𝒪_Y)`, equivalently `ringedToposHom f` with inverse-image
structure map `commInverseImageStructureSheafMap f`, is flat. -/
@[stacks 073C]
theorem flat_iff_isFlatHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    Flat f ↔ IsFlatHom.{u + 1, u, u} (commInverseImageStructureSheafMap f) :=
  sorry

/-- A flat morphism of algebraic spaces has flat associated inverse-image
structure-sheaf map `f^♯`. -/
theorem isFlatHom_of_flat {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Flat f] :
    IsFlatHom.{u + 1, u, u} (commInverseImageStructureSheafMap f) :=
  sorry

/-- A morphism of algebraic spaces whose associated inverse-image
structure-sheaf map `f^♯` is flat is itself flat. -/
theorem Flat.of_isFlatHom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y)
    (h : IsFlatHom.{u + 1, u, u} (commInverseImageStructureSheafMap f)) :
    Flat f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
