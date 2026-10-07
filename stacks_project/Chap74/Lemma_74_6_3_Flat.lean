module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap67.Lemma_67_31_3_FlatOver
public import stacks_project.Chap73.Definition_73_9_1_FpqcCovering

/-!
# Flat modules on algebraic spaces

An `𝒪_X`-module on an algebraic space is flat when it is relatively flat over `X`
along the identity morphism. Flatness of quasi-coherent modules descends along
fpqc covering families.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u v

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- An `𝒪_X`-module on an algebraic space is flat when it is flat over `X` along
the identity morphism. -/
class IsFlat {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) : Prop where
  /-- Absolute flatness is relative flatness along `𝟙 X`. -/
  flatOver_id : flatOver F (𝟙 X)

/-- Absolute flatness of an `𝒪_X`-module is equivalent to relative flatness along `𝟙 X`. -/
theorem isFlat_iff_flatOver_id {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    IsFlat F ↔ flatOver F (𝟙 X) := sorry

/-- The structure sheaf of an algebraic space is a flat module. -/
instance unit_isFlat {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsFlat (SheafOfModules.unit (structureSheaf X)) := sorry

namespace IsFlat

/-- A quasi-coherent module on an algebraic space is flat if its pullbacks along an
fpqc covering family are flat. -/
theorem of_fpqcCovering {S : Scheme.{u}} {X : AlgebraicSpace S} {ι : Type v}
    (F : X.Modules) [F.IsQuasicoherent] (family : ι → Over X)
    (hfamily : FpqcCovering family)
    (hpullback : ∀ i, IsFlat ((pullback (family i).hom).obj F)) :
    IsFlat F := sorry

end IsFlat

end AlgebraicGeometry.AlgebraicSpace.Modules
