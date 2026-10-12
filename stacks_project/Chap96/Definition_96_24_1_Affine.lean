/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Sites.Sheaf
public import ReasLib.AlgebraicGeometry.Scheme.Sites.AffineOver
public import stacks_project.Chap94.Definition_94_12_1_Representable

/-!
# Associated affine site of a category fibred in groupoids

The associated affine site of a category fibred in groupoids `X` over
`(Sch/S)_fppf` is the full subcategory of objects lying over an affine scheme,
equipped with the chaotic topology.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty

universe u w

namespace AlgebraicGeometry.GroupoidsOver

variable {S : Scheme.{u}}

/-- Objects of a category fibred in groupoids that lie over an affine scheme. -/
abbrev affineObjects (X : GroupoidsOver S) : ObjectProperty X.total :=
  (Scheme.affineOverProperty S).inverseImage X.p

/-- An object of `X` lies in `affineObjects X` if and only if the scheme it
lies over is affine. -/
theorem mem_affineObjects_iff (X : GroupoidsOver S) (x : X.total) :
    affineObjects X x ↔ IsAffine (X.p.obj x).left :=
  sorry

/-- The full subcategory `𝒳_affine` of objects of `X` lying over an affine
scheme. -/
abbrev Affine (X : GroupoidsOver S) :=
  (affineObjects X).FullSubcategory

/-- The inclusion of the associated affine site into the total category of
`X`. -/
abbrev affineInclusion (X : GroupoidsOver S) : Affine X ⥤ X.total :=
  (affineObjects X).ι

/-- The inclusion of an object of the associated affine site is its underlying
object in the total category of `X`. -/
theorem affineInclusion_obj (X : GroupoidsOver S) (x : Affine X) :
    (affineInclusion X).obj x = x.obj :=
  sorry

/-- Every object of the associated affine site lies over an affine scheme. -/
instance instIsAffine (X : GroupoidsOver S) (x : Affine X) :
    IsAffine (X.p.obj x.obj).left :=
  x.property

/-- Construct an object of the associated affine site from an object of `X`
lying over an affine scheme. -/
def Affine.mk {X : GroupoidsOver S} (x : X.total)
    (hx : IsAffine (X.p.obj x).left) : Affine X :=
  ⟨x, hx⟩

/-- The underlying object of `Affine.mk x hx` is `x`. -/
theorem Affine.mk_obj {X : GroupoidsOver S} (x : X.total)
    (hx : IsAffine (X.p.obj x).left) : (Affine.mk x hx).obj = x :=
  sorry

/-- The chaotic topology on the associated affine site of `X`. -/
abbrev affineTopology (X : GroupoidsOver S) : GrothendieckTopology (Affine X) :=
  ⊥

/-- The topology of the associated affine site is the chaotic topology. -/
theorem affineTopology_eq_bot (X : GroupoidsOver S) :
    affineTopology X = ⊥ :=
  sorry

/-- Every presheaf on the associated affine site is a sheaf for the chaotic
topology. -/
theorem isSheaf_affineTopology (X : GroupoidsOver S) {A : Type w}
    [Category.{u} A] (P : (Affine X)ᵒᵖ ⥤ A) :
    Presheaf.IsSheaf (affineTopology X) P :=
  sorry

/-- Sheaves on the associated affine site are the same as presheaves. -/
abbrev affineSheafEquivalence (X : GroupoidsOver S) (A : Type w)
    [Category.{u} A] :
    Sheaf (affineTopology X) A ≌ (Affine X)ᵒᵖ ⥤ A :=
  sheafBotEquivalence A

/-- `affineSheafEquivalence X A` is the canonical equivalence between sheaves
for the chaotic topology on `Affine X` and presheaves on `Affine X`. -/
theorem affineSheafEquivalence_eq (X : GroupoidsOver S) (A : Type w)
    [Category.{u} A] :
    affineSheafEquivalence X A = sheafBotEquivalence A :=
  sorry

end AlgebraicGeometry.GroupoidsOver
