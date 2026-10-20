module

public import Mathlib.CategoryTheory.ComposableArrows.Basic
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.Scheme.Branch
public import ReasLib.AlgebraicGeometry.Scheme.Modification.Elementary
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Multicross
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization
public import ReasLib.AlgebraicGeometry.Scheme.Regular

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.SchemeOverField

/-- For a closed singular point on a reduced algebraic one-dimensional scheme over an
algebraically closed field, multicrossness, the delta-branch equality, and a resolution by
successive gluings of two points are equivalent. -/
theorem isMulticrossSingularity_tfae
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [Algebraic X] [IsReduced X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (x : X.left) (h_closed : x ∈ closedPoints X.left)
    (h_singular : ¬ X.hom.SmoothAt x)
    (Ah : Type v) [CommRing Ah] [Algebra (stalkRing X x) Ah]
    [IsHenselizationOf (stalkRing X x) Ah] :
    List.TFAE
      [ isMulticrossSingularity X x
      , deltaInvariantAt X x = X.left.branchNumberAt x Ah - 1
      , ∃ (n : ℕ) (U : X.left.Opens)
          (D : ComposableArrows (SchemeOverField k) n)
          (h_alg : ∀ i : Fin (n + 1), Algebraic (D.obj i)),
          ∃ (e_target : D.right ≅ Over.mk (U.ι ≫ X.hom)),
            x ∈ U ∧ Scheme.Regular D.left.left ∧
              ∀ i : Fin n,
                ∃ (a b : SchemeOverField.point k ⟶ D.obj i.castSucc)
                  (y : SchemeOverField.point k ⟶ D.obj i.succ)
                  (V : (D.obj i.succ).left.Opens)
                  (evalA evalB :
                    (TopCat.Sheaf.pushforward CommRingCat
                      (D.map' i.1 (i.1 + 1)).left.base).obj
                      (D.obj i.castSucc).left.sheaf ⟶
                      pointRingSheaf (D.obj i.succ).left
                        (SchemeOverField.rationalPoint y
                          (IsLocalRing.closedPoint k)) k),
                  GlueingPoints (D.obj i.castSucc) (D.obj i.succ)
                    (h_alg i.castSucc) (h_alg i.succ)
                    (D.map' i.1 (i.1 + 1)) a b y V evalA evalB ] := sorry

end AlgebraicGeometry.SchemeOverField

end
