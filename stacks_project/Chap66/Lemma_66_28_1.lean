module

public import ReasLib.Algebra.Category.Ring.Sheaf.LocalHom
public import stacks_project.Chap66.Lemma_66_28_1_Hom

/-!
# Lemma 66.28.1

The morphism of small étale ringed topoi associated to a morphism of algebraic spaces is a
morphism of locally ringed topoi in the sense of Modules on Sites, Definition 18.40.9.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Sheaf.LocalHom

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Lemma 66.28.1: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, the
associated morphism of small étale ringed topoi `(f_small, f^♯)`, packaged as
`ringedToposHom f`, is a morphism of locally ringed topoi in the sense of
Definition 18.40.9, i.e. `Sheaf.LocalHom.IsLocal` of the inverse-image structure-sheaf map
`f^♯`. -/
@[stacks 04KJ, instance]
instance commInverseImageStructureSheafMap_isLocal (f : X ⟶ Y) :
    IsLocal (commInverseImageStructureSheafMap f) :=
  sorry

/-- Locality of `commInverseImageStructureSheafMap f` is objectwise locality of the
inverse-image structure-sheaf map, matching Definition 18.40.9. -/
theorem commInverseImageStructureSheafMap_isLocal_iff (f : X ⟶ Y) :
    IsLocal (commInverseImageStructureSheafMap f) ↔
      ∀ U : (smallEtaleSite X)ᵒᵖ,
        IsLocalHom ((commInverseImageStructureSheafMap f).hom.app U).hom :=
  sorry

/-- The units square of `f^♯` is cartesian objectwise, the literal diagram of
Definition 18.40.9. -/
theorem commInverseImageStructureSheafMap_unitsSquareCartesian (f : X ⟶ Y) :
    UnitsSquareCartesian (commInverseImageStructureSheafMap f) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
