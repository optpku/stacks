module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
import StacksCheckRecall

/-!
# Definition 29.16.3

The finite type point predicate and its set-level API are owned by
`ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point`.

@stack 02J1
-/

@[expose] public section

universe u

/- Definition 29.16.3
A point of a scheme is a finite type point when its canonical residue-field morphism is of finite
type. The finite type points form a set in the underlying space of the scheme.
-/
@[stacks 02J1] #check (@AlgebraicGeometry.IsFiniteTypePoint :
  {S : AlgebraicGeometry.Scheme.{u}} → S → Prop)

#check (@AlgebraicGeometry.isFiniteTypePoint_iff :
  {S : AlgebraicGeometry.Scheme.{u}} → (s : S) →
    AlgebraicGeometry.IsFiniteTypePoint s ↔
      AlgebraicGeometry.Scheme.Hom.FiniteType (S.fromSpecResidueField s))

#check (@AlgebraicGeometry.finiteTypePoints :
  (S : AlgebraicGeometry.Scheme.{u}) → Set S)

#check (@AlgebraicGeometry.mem_finiteTypePoints_iff :
  (S : AlgebraicGeometry.Scheme.{u}) → (s : S) →
    s ∈ AlgebraicGeometry.finiteTypePoints S ↔ AlgebraicGeometry.IsFiniteTypePoint s)
