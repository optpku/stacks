module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

open RationalTail

/- Example 53.23.1 (Contracting a rational tail) (1): a rational tail records the selected component,
its unique reduced attachment, bijective evaluation, and genus-zero condition. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail :
    ∀ {k : Type u} [Field k], SchemeOverField k → Type u)

/- Example 53.23.1 (Contracting a rational tail) (2): the canonical morphism over the base field
contracts the selected component onto the complementary closure. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.contraction :
    ∀ {k : Type u} [Field k] {X : SchemeOverField k} [IsReduced X.left]
      (T : RationalTail X), X ⟶ complementOver X T.component)

/- Example 53.23.1 (Contracting a rational tail) (3): the attachment point is a node of `X`. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.attachment_isNode :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      isNode X T.attachmentPoint)

/- Example 53.23.1 (Contracting a rational tail) (4): the attachment residue field is finite
over the base field. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.attachmentField_finite :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      FiniteDimensional k (X.left.residueField T.attachmentPoint))

/- Example 53.23.1 (Contracting a rational tail) (5): the attachment residue field is separable
over the base field. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.attachmentField_separable :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      Algebra.IsSeparable k (X.left.residueField T.attachmentPoint))

/- Example 53.23.1 (Contracting a rational tail) (6): the contraction restricts to the identity
on the complementary closure. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.restricts_to_complement :
    ∀ {k : Type u} [Field k]
      {X : SchemeOverField k} [IsReduced X.left]
    (T : RationalTail X),
      (complementIdeal X T.component).subschemeι ≫ T.contraction.left = 𝟙 _)

/- Example 53.23.1 (Contracting a rational tail) (7): the contraction restricts to the component
collapse on the rational tail. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.restricts_to_component :
    ∀ {k : Type u} [Field k]
      {X : SchemeOverField k} [IsReduced X.left]
    (T : RationalTail X),
      (componentIdeal X T.component).subschemeι ≫ T.contraction.left = T.collapse)

/- Example 53.23.1 (Contracting a rational tail) (8): the canonical structure-sheaf
pushforward map of the contraction is an isomorphism. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.pushforward_iso :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [IsReduced X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      IsIso (commRingSheafPushforwardMap T.contraction.left.toShHom))

/- Example 53.23.1 (Contracting a rational tail) (9): the first higher direct image of the
structure sheaf under the contraction vanishes. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.higherDirectImage_one_isZero :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom] [IsReduced X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      IsZero (higherDirectImageModule T.contraction.left.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf) 1))

/- Example 53.23.1 (Contracting a rational tail) (10): the complementary closure is proper over
the base field. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.complement_proper :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      IsProper (complementOver X T.component).hom)

/- Example 53.23.1 (Contracting a rational tail) (11): the complementary closure is
one-dimensional. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.complement_dimension :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      topologicalKrullDim (complementOver X T.component).left = 1)

/- Example 53.23.1 (Contracting a rational tail) (12): the complementary closure is
at-worst-nodal. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.complement_atWorstNodal :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      atWorstNodal (complementOver X T.component))

/- Example 53.23.1 (Contracting a rational tail) (13): the complementary closure has the same
global functions as the base field. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.complement_globalSections :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      Function.Bijective (Scheme.Hom.globalSectionsMap (complementOver X T.component).hom))

/- Example 53.23.1 (Contracting a rational tail) (14): contraction preserves the genus. -/
@[stacks 0E3H] #check
  (AlgebraicGeometry.SchemeOverField.RationalTail.genus_eq :
    ∀ {k : Type u} [Field k]
      (X : SchemeOverField k) [Algebraic X] [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_global : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X) (T : RationalTail X),
      Scheme.Hom.cohomologyFinrank (complementOver X T.component).hom
        (SheafOfModules.unit (complementOver X T.component).left.ringCatSheaf) 1 =
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf) 1)

end AlgebraicGeometry.SchemeOverField
