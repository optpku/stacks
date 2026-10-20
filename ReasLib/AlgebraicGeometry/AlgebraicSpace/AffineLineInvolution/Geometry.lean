module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FunctionField
public import ReasLib.Topology.KrullDimension.Local
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Geometry of the affine-line involution quotient

Geometric properties of the punctured-negation quotient, its atlas topology, and
rational-function pullback along squaring and negation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits
open AlgebraicGeometry.Scheme

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution

/-- The affine line over `k` is an integral scheme. -/
instance instIsIntegral_cover (k : Type u) [Field k] :
    AlgebraicGeometry.IsIntegral (cover k).left := by
  change AlgebraicGeometry.IsIntegral
    (AffineSpace (ULift.{u} (Fin 1)) (Spec (CommRingCat.of k)))
  infer_instance

/-- The affine line over `k` is a locally Noetherian scheme. -/
instance instIsLocallyNoetherian_cover (k : Type u) [Field k] :
    AlgebraicGeometry.IsLocallyNoetherian (cover k).left := sorry

/-- The affine line over `k` is a Noetherian scheme. -/
instance instIsNoetherian_cover (k : Type u) [Field k] :
    AlgebraicGeometry.IsNoetherian (cover k).left := sorry

/-- The top open of the affine line is nonempty. -/
instance instNonempty_top_cover (k : Type u) [Field k] :
    Nonempty (⊤ : (cover k).left.Opens) :=
  ⟨⟨genericPoint (cover k).left, Set.mem_univ _⟩⟩

/-- The structure morphism of `𝔸¹_k` commutes with the identity of `Spec k`. -/
theorem coverToBase_w (k : Type u) [Field k] :
    (cover k).hom ≫ (Over.mk (𝟙 (base k))).hom = (cover k).hom := sorry

/-- The structure morphism `𝔸¹_k ⟶ Spec k` as a morphism of objects over `Spec k`. -/
def coverToBase (k : Type u) [Field k] : cover k ⟶ Over.mk (𝟙 (base k)) :=
  Over.homMk (cover k).hom (coverToBase_w k)

/-- The underlying scheme morphism of `coverToBase` is the structure map of the affine line. -/
theorem coverToBase_left (k : Type u) [Field k] :
    (coverToBase k).left = (cover k).hom := sorry

/-- The involution relation equalizes the structure morphism of the affine line. -/
theorem coverToBase_equalizes (k : Type u) [Field k] :
    (preRelation k).t ≫ coverToBase k = (preRelation k).s ≫ coverToBase k := sorry

/-- The structure morphism `X ⟶ Spec k` of the affine-line involution space. -/
def toBase (k : Type u) [Field k] :
    sheafOfPoints k ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (Over.mk (𝟙 (base k))) :=
  (preRelation k).quotientSheafDesc (Scheme.fppfTopology.over (base k))
    (coverToBase k) (coverToBase_equalizes k)

/-- `toBase` is the quotient-sheaf descent of `coverToBase`. -/
theorem toBase_eq (k : Type u) [Field k] :
    toBase k =
      (preRelation k).quotientSheafDesc (Scheme.fppfTopology.over (base k))
        (coverToBase k) (coverToBase_equalizes k) := sorry

/-- On the atlas, `toBase` recovers the structure morphism of `𝔸¹_k`. -/
theorem toBase_comp_atlas (k : Type u) [Field k] :
    atlas k ≫ toBase k =
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map (coverToBase k) :=
  sorry

/-- The étale-square smoothness criterion for the structure morphism `toBase`:
every commutative square with étale vertical arrows from schemes has smooth
top arrow. This is not representable smoothness of `toBase`. -/
def isSmoothOverBase (k : Type u) [Field k] : Prop :=
  ∀ {U V : Over (base k)}
    (a : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj U ⟶ sheafOfPoints k)
    (b : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj V ⟶
      (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj (Over.mk (𝟙 (base k))))
    (h : U ⟶ V),
    (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} a.hom →
      (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} b.hom →
        a ≫ toBase k =
            (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.map h ≫ b →
          AlgebraicGeometry.Smooth h.left

/-- The affine-line involution quotient is smooth over its base field in the étale-square sense. -/
theorem smooth_toBase (k : Type u) [Field k] [NeZero (2 : k)] :
    isSmoothOverBase k :=
  sorry



/-- The involution quotient has a Noetherian atlas and a quasi-compact diagonal.
Together with the étale-surjective atlas, these certify Noetherianity of the quotient. -/
theorem isNoetherian (k : Type u) [Field k] [NeZero (2 : k)] :
    AlgebraicGeometry.IsNoetherian (cover k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) :=
  sorry

/-- The involution quotient has an integral atlas and a quasi-compact diagonal.
The étale-surjective atlas gives reducedness, its image is irreducible, and the
quasi-compact diagonal certifies quasi-separatedness and decency. -/
theorem isIntegral (k : Type u) [Field k] [NeZero (2 : k)] :
    AlgebraicGeometry.IsIntegral (cover k).left ∧
      (MorphismProperty.over (@QuasiCompact)).relative uliftYoneda.{u + 1}
        (diag (sheafOfPoints k).obj) :=
  sorry

/-- The étale-local dimension of `X`, as the supremum of local topological Krull
dimensions along étale scheme charts of `sheafOfPoints`. -/
def dimension (k : Type u) [Field k] : WithBot ℕ∞ :=
  ⨆ (U : Over (base k))
    (f : (Scheme.fppfTopology.over (base k)).uliftYoneda.{u + 1}.obj U ⟶ sheafOfPoints k)
    (hf : (MorphismProperty.over (@Etale)).relative uliftYoneda.{u + 1} f.hom)
    (u : U.left), topologicalKrullDimAt u

/-- The étale-local dimension of the affine-line involution quotient is one. -/
theorem dimension_eq_one (k : Type u) [Field k] [NeZero (2 : k)] :
    dimension k = 1 :=
  sorry

/-- Two atlas points have the same square image exactly when a relation point joins them. -/
theorem squareMap_fiber_iff_relation (k : Type u) [Field k] [NeZero (2 : k)]
    (x y : (cover k).left) :
    (squareOver k).left x = (squareOver k).left y ↔
      ∃ r : (preRelation k).left.left,
        (preRelation k).t.left r = x ∧ (preRelation k).s.left r = y := sorry

/-- The underlying squaring map of the affine line is a quotient map. -/
theorem isQuotientMap_squareOver (k : Type u) [Field k] [NeZero (2 : k)] :
    Topology.IsQuotientMap (squareOver k).left := sorry

/-- Squaring sends the generic point of the affine line to itself. -/
theorem squareOver_genericPoint (k : Type u) [Field k] :
    (squareOver k).left (genericPoint (cover k).left) = genericPoint (cover k).left := sorry

/-- Negation sends the generic point of the affine line to itself. -/
theorem involution_genericPoint (k : Type u) [Field k] :
    (involution k).left (genericPoint (cover k).left) = genericPoint (cover k).left := sorry

/-- Pullback of rational functions along the squaring map of the affine line. -/
def squareFunctionFieldMap (k : Type u) [Field k] :
    (cover k).left.functionField →+* (cover k).left.functionField :=
  (squareOver k).left.functionFieldMap (squareOver_genericPoint k)

/-- Pullback of rational functions along negation on the affine line. -/
def involutionFunctionFieldMap (k : Type u) [Field k] :
    (cover k).left.functionField →+* (cover k).left.functionField :=
  (involution k).left.functionFieldMap (involution_genericPoint k)

/-- A rational function descends along squaring precisely when negation fixes it. -/
theorem mem_range_squareFunctionFieldMap_iff (k : Type u) [Field k] [NeZero (2 : k)]
    (f : (cover k).left.functionField) :
    f ∈ Set.range (squareFunctionFieldMap k) ↔ involutionFunctionFieldMap k f = f := sorry

end AlgebraicGeometry.AlgebraicSpace.AffineLineInvolution
