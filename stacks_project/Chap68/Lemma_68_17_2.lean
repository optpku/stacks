module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable

/-!
# Implications among relative conditions

A morphism of algebraic spaces that is representable or quasi-separated is very
reasonable, and very reasonableness implies reasonableness, decency, and
property (β).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace VeryReasonable

/-- Lemma 68.17.2 (1): a representable morphism `f : X ⟶ Y` of algebraic spaces
over a scheme `S`, in the sense `yoneda.relativelyRepresentable f`, is very
reasonable. -/
@[stacks 03M5]
theorem of_relativelyRepresentable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (hf : yoneda.relativelyRepresentable f) : VeryReasonable f :=
  sorry

/-- Lemma 68.17.2 (2): a quasi-separated morphism of algebraic spaces over a
scheme is very reasonable. -/
@[stacks 03M5, instance 900]
instance of_quasiSeparated {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [QuasiSeparated f] : VeryReasonable f :=
  sorry

end VeryReasonable

namespace Reasonable

/-- Lemma 68.17.2 (3): a very reasonable morphism of algebraic spaces over a
scheme is reasonable. -/
@[stacks 03M5, instance 900]
instance of_veryReasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [VeryReasonable f] : Reasonable f :=
  sorry

end Reasonable

namespace Decent

/-- Lemma 68.17.2 (4): a reasonable morphism of algebraic spaces over a scheme
is decent. -/
@[stacks 03M5, instance 900]
instance of_reasonable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Reasonable f] : Decent f :=
  sorry

end Decent

namespace PropertyBeta

/-- Lemma 68.17.2 (5): a decent morphism of algebraic spaces over a scheme has
property (β). -/
@[stacks 03M5, instance 900]
instance of_decent {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Decent f] : PropertyBeta f :=
  sorry

end PropertyBeta

end AlgebraicGeometry.AlgebraicSpace
